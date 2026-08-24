#!/usr/bin/env bash
#
# Delete the GitHub Actions cache entries that nothing will ever read again.
#
# A repository gets one 10GB Actions cache allowance, shared by every key any
# workflow writes. Two habits of ci.yml consume it without bound:
#
#   - The ccache keys end in ${{ github.run_id }}. They have to: a cache key
#     cannot be updated in place, so writing a fresh one per run and letting
#     restore-keys pick the newest is the only way to carry a compiler cache
#     forward. But every run leaves its predecessor behind, and only the newest
#     is ever restored.
#
#   - A pull request writes its caches under refs/pull/<n>/merge. Merging or
#     closing it does not remove them, and no later run can read them: cache
#     reads see the current ref and the default branch, never another branch.
#
# Left alone the allowance fills, GitHub evicts whatever is least recently
# used, and unrelated keys -- the sccache objects the Windows legs write, the
# dependency trees -- are what get thrown out.
#
# So: keep the newest ccache entry per (ref, key prefix), drop the rest, and
# drop everything belonging to a pull request that is no longer open. Content
# keyed entries are left alone entirely, because a hit on one still means it is
# valid: deps-*, codeql-*, msys2-*, and the individual sccache objects, whose
# keys are hashes of what they hold rather than of when they were written.
#
# Deleting an entry that is not the newest cannot make a concurrent run miss:
# restore-keys resolves to the newest match, which is the one kept.
#
#     scripts/prune-ci-caches.sh --dry-run    # report, delete nothing
#     scripts/prune-ci-caches.sh
#
# Needs gh authenticated with actions:write to delete, and pull-requests:read
# to tell an open pull request from a closed one.

set -u -o pipefail

dry_run=0
case "${1-}" in
    --dry-run) dry_run=1 ;;
    "") ;;
    *) echo "usage: $0 [--dry-run]" >&2; exit 2 ;;
esac

repo=${GITHUB_REPOSITORY:-$(gh repo view --json nameWithOwner --jq .nameWithOwner)}
if [ -z "$repo" ]; then
    echo "error: no repository; set GITHUB_REPOSITORY or run inside a checkout" >&2
    exit 1
fi
echo "repository: $repo"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# id, ref, key, created_at, size. Sizes are what GitHub bills against the
# allowance, so they are what the report below adds up.
if ! gh api --paginate "repos/$repo/actions/caches?per_page=100" \
        --jq '.actions_caches[] | [.id, .ref, .key, .created_at, .size_in_bytes] | @tsv' \
        > "$work/raw.tsv"; then
    echo "error: could not list caches" >&2
    exit 1
fi

# The listing is paginated over a set that a running workflow is still adding
# to, so an entry can shift across a page boundary and be returned twice --
# 1751 rows for 1740 caches, when this was written. Deleting a duplicate is
# harmless, but counting one is not, so the id decides and the report is honest.
sort -u -t"$(printf '\t')" -k1,1 "$work/raw.tsv" > "$work/all.tsv"

# The full listing carries size in column 5; the shortlists below are pairs of
# id and size, so the column is named rather than assumed.
report() {
    awk -F'\t' -v label="$1" -v column="$3" '
        { bytes += $column; n++ }
        END { printf "%s: %d entries, %.2f GB\n", label, n, bytes / 1073741824 }
    ' "$2"
}
report "in the cache" "$work/all.tsv" 5

# Superseded compiler caches. The key is <prefix>/<run id>; strip the run id to
# get the group, sort each group newest first, and mark everything after the
# first. Restricted to ccache-* because that is the family whose key encodes
# when it was written rather than what it contains -- applying this to a
# content-keyed family would delete live entries.
#
# Either separator is accepted. The keys used to be <prefix>-<run id>, and a
# hyphen there was what let one leg's restore-keys reach into another's
# entries; entries written before that changed are still here, still worth
# pruning, and group with their replacements because stripping either
# separator leaves the same prefix.
awk -F'\t' '$3 ~ /^ccache-.+[-\/][0-9]+$/ {
    prefix = $3
    sub(/[-\/][0-9]+$/, "", prefix)
    print $2 "\t" prefix "\t" $4 "\t" $1 "\t" $5
}' "$work/all.tsv" |
    sort -t"$(printf '\t')" -k1,1 -k2,2 -k3,3r |
    awk -F'\t' '
        { group = $1 "\t" $2; if (group == previous) print $4 "\t" $5; previous = group }
    ' > "$work/superseded.tsv"
report "superseded compiler caches" "$work/superseded.tsv" 2

# Caches belonging to pull requests that are no longer open. Each number is
# asked about once; a request that 404s (deleted fork, say) is treated as
# closed, since nothing can read its caches either way.
: > "$work/abandoned.tsv"
awk -F'\t' '$2 ~ /^refs\/pull\/[0-9]+\//' "$work/all.tsv" > "$work/pull.tsv"
sed 's#^[^\t]*\trefs/pull/\([0-9]*\)/.*#\1#' "$work/pull.tsv" | sort -un > "$work/numbers.txt"
while read -r number; do
    [ -n "$number" ] || continue
    state=$(gh api "repos/$repo/pulls/$number" --jq .state 2>/dev/null || echo closed)
    [ "$state" = open ] && continue
    awk -F'\t' -v n="$number" '$2 == "refs/pull/" n "/merge" || $2 == "refs/pull/" n "/head" {
        print $1 "\t" $5
    }' "$work/pull.tsv" >> "$work/abandoned.tsv"
done < "$work/numbers.txt"
report "caches of closed pull requests" "$work/abandoned.tsv" 2

# A closed pull request's newest entry is in both lists.
sort -u "$work/superseded.tsv" "$work/abandoned.tsv" > "$work/doomed.tsv"
report "to delete" "$work/doomed.tsv" 2

if [ "$dry_run" -eq 1 ]; then
    echo "--dry-run: nothing deleted"
    exit 0
fi

failed=0
deleted=0
while IFS=$'\t' read -r id _size; do
    [ -n "$id" ] || continue
    if gh api --method DELETE "repos/$repo/actions/caches/$id" --silent 2>/dev/null; then
        deleted=$((deleted + 1))
    else
        # Another prune, or GitHub's own eviction, may have taken it first.
        # That is the outcome this wanted, so it is not a failure.
        failed=$((failed + 1))
    fi
done < "$work/doomed.tsv"

echo "deleted $deleted, already gone $failed"

# What the allowance looks like afterwards, from GitHub rather than from
# subtraction, so the number reflects deletions this run did not make.
gh api "repos/$repo/actions/cache/usage" \
    --jq '"remaining: \(.active_caches_count) entries, \(.active_caches_size_in_bytes / 1073741824 * 100 | round / 100) GB"'
