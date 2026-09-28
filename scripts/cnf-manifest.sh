#!/usr/bin/env bash
#
# Emit a manifest of the CNF an stp binary generates over a corpus: one line
# per input file, sorted, of the form
#
#     <sha256 | none | timeout | error>  <path relative to the corpus root>
#
# The CNF STP produces is a function of the input alone. Nothing about how the
# binary was built -- which compiler, which optimisation level, which
# allocator, 32- or 64-bit, static or shared -- should reach it. Where it does,
# the cause is something reading an address rather than a value: iteration over
# a hash table keyed on pointers, a sort that ties on node identity, an
# uninitialised read. Those are exactly the bugs that make a performance
# measurement irreproducible and a bug report unrepeatable, and they are
# invisible to a test suite that only checks sat/unsat.
#
# So: run this against two builds and diff the manifests. Identical means the
# CNF is byte-identical across the pair for every input in the corpus.
#
#     scripts/cnf-manifest.sh build-gcc/stp tests/query-files > gcc.manifest
#     scripts/cnf-manifest.sh build-clang/stp tests/query-files > clang.manifest
#     diff -u gcc.manifest clang.manifest
#
# A differing line names the input that provokes it, which is the thing you
# need to debug it.

set -u -o pipefail

if [ $# -lt 2 ]; then
    echo "usage: $0 <stp binary> <corpus directory> [timeout seconds] [stp arg ...]" >&2
    exit 2
fi

solver=$(readlink -f "$1")
corpus=$(readlink -f "$2")
per_file_timeout=${3:-60}
# Anything further is handed to stp. The paths this pass touches are mostly
# off by default -- --aig-core-simplification, --aig-rewrite-passes,
# --disable-simplifications -- so a manifest taken without them proves nothing
# about the code they reach.
if [ $# -gt 3 ]; then shift 3; extra_args=("$@"); else extra_args=(); fi

if [ ! -x "$solver" ]; then
    echo "$0: '$1' is not an executable" >&2
    exit 2
fi
if [ ! -d "$corpus" ]; then
    echo "$0: '$2' is not a directory" >&2
    exit 2
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# --output-CNF writes output_<n>.cnf into the working directory, so each input
# gets a clean one. --exit-after-CNF stops at the first, which keeps the run
# bounded on array problems whose refinement loop would otherwise emit one per
# round; the first CNF is the one every build has to agree on anyway.
#
# --array-equality because STP refuses a whole-array equality outright without
# it, and the corpus has 79 such inputs that would otherwise contribute an
# identical "error" line from every build and test nothing. It is a semantic
# option that only bites on formulas containing such an equality: measured
# inert -- byte-identical CNF -- on all 111 corpus inputs that generate one
# without it.
#
# find | sort rather than a glob: the manifest has to be in a stable order for
# diff to be readable, and locale-independent so two machines agree.
while IFS= read -r input; do
    rel=${input#"$corpus"/}
    rm -rf "$work/run"
    mkdir -p "$work/run"

    # Run first and capture the status separately: inside `if ! cmd; then`,
    # $? is the status of the negation -- always 0 there -- not the command's,
    # so every timeout used to be recorded as an error.
    (cd "$work/run" && timeout "$per_file_timeout" \
         "$solver" --array-equality --output-CNF --exit-after-CNF \
         ${extra_args+"${extra_args[@]}"} "$input" \
         >/dev/null 2>&1)
    status=$?
    if [ "$status" -ne 0 ]; then
        # 124 is timeout(1) killing it. Anything else is stp declining the
        # input -- an unsupported logic, a deliberate error-path test. Both
        # are recorded rather than skipped: a build that starts timing out, or
        # starts rejecting an input the others accept, is itself a difference
        # worth seeing.
        if [ "$status" -eq 124 ]; then
            printf '%-64s  %s\n' timeout "$rel"
        else
            printf '%-64s  %s\n' error "$rel"
        fi
        continue
    fi

    # Concatenated in name order, so a problem that emits several CNFs still
    # hashes to one value. No CNF at all is the normal outcome for an input
    # the preprocessing simplifier settles on its own, and is itself a fact
    # the builds must agree on.
    cnfs=$(find "$work/run" -maxdepth 1 -name 'output_*.cnf' | LC_ALL=C sort)
    if [ -z "$cnfs" ]; then
        printf '%-64s  %s\n' none "$rel"
    else
        # shellcheck disable=SC2086
        printf '%-64s  %s\n' "$(cat $cnfs | sha256sum | cut -d' ' -f1)" "$rel"
    fi
done < <(find "$corpus" -type f \( -name '*.smt2' -o -name '*.cvc' \) \
             | LC_ALL=C sort)
