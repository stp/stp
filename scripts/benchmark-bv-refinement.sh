#!/usr/bin/env bash
# Compare BV-refinement configurations over a directory or a manifest of
# standalone SMT-LIB2 queries. Runs are blocked by (repetition, query), with
# the variant order rotated inside each block so machine drift does not
# systematically favour one setting.

set -u
set -o pipefail
export LC_ALL=C

usage()
{
  cat <<'EOF'
Usage: benchmark-bv-refinement.sh --solver PATH (--corpus DIR | --list FILE) [options] [-- STP_ARG ...]

Required:
  --solver PATH          STP executable to measure
  --corpus DIR           directory containing *.smt2 query files, or
  --list FILE            query paths, one per line; relative paths are
                         resolved from the list's directory

Options:
  --output DIR           new result directory (default: a directory in /tmp)
  --repetitions N        complete blocked repetitions (default: 1)
  --timeout SECONDS      per-query wall-clock cap (default: 20)
  --limits LIST          comma-separated value limits (default: 4,8,16,32)
  --profiles LIST        compare named profiles instead of value limits; the
                         first comma-separated profile is the reference
  --variant NAME:FLAGS   arbitrary named configuration; repeatable, with the
                         first variant as reference. FLAGS are whitespace-
                         separated STP arguments without shell quoting
  --width BITS           abstraction width floor (default: 53)
  --backend NAME         minisat, cadical, or default (default: minisat)
  --split-fp             classify queries as fp or bv (the default)
  --no-split-fp          put every query in one all class
  --no-exact-control     omit the abstraction-off control
  --no-uncapped-control  omit the uncapped-allowance control
  --help                 show this text

Allowance mode selects the qualified profile explicitly. Profile mode runs
each requested atomic profile with its own round limit. Both modes always
request quick statistics. Arguments after -- are passed unchanged to every
STP run. Custom --variant mode runs exactly the configurations supplied and
is mutually exclusive with allowance/profile controls; use arguments after
-- for settings common to every custom variant.
The result directory contains runs.tsv, records.tsv, summary.tsv,
comparisons.tsv, comparison-summary.tsv, disagreements.tsv, metadata.txt,
corpus.sha256, and one raw log per run. In allowance mode comparisons use the
uncapped control as their reference when it is enabled, or the first profile
in profile mode. The first named custom variant is the reference in custom
mode.
EOF
}

die()
{
  printf 'benchmark-bv-refinement: %s\n' "$*" >&2
  exit 2
}

solver=
corpus=
list=
output=
repetitions=1
timeout_seconds=20
limits_csv=4,8,16,32
profiles_csv=
limits_explicit=0
width_explicit=0
controls_explicit=0
width=53
backend=minisat
include_exact=1
include_uncapped=1
split_fp=1
custom_variant_specs=()
extra_args=()

while (($# > 0)); do
  case "$1" in
    --solver)
      (($# >= 2)) || die '--solver needs a path'
      solver=$2
      shift 2
      ;;
    --corpus)
      (($# >= 2)) || die '--corpus needs a directory'
      corpus=$2
      shift 2
      ;;
    --list)
      (($# >= 2)) || die '--list needs a file'
      list=$2
      shift 2
      ;;
    --output)
      (($# >= 2)) || die '--output needs a directory'
      output=$2
      shift 2
      ;;
    --repetitions)
      (($# >= 2)) || die '--repetitions needs a positive integer'
      repetitions=$2
      shift 2
      ;;
    --timeout)
      (($# >= 2)) || die '--timeout needs a positive number of seconds'
      timeout_seconds=$2
      shift 2
      ;;
    --limits)
      (($# >= 2)) || die '--limits needs a comma-separated list'
      limits_csv=$2
      limits_explicit=1
      shift 2
      ;;
    --profiles)
      (($# >= 2)) || die '--profiles needs a comma-separated list'
      profiles_csv=$2
      shift 2
      ;;
    --variant)
      (($# >= 2)) || die '--variant needs NAME:FLAGS'
      custom_variant_specs+=("$2")
      shift 2
      ;;
    --width)
      (($# >= 2)) || die '--width needs a positive integer'
      width=$2
      width_explicit=1
      shift 2
      ;;
    --backend)
      (($# >= 2)) || die '--backend needs minisat, cadical, or default'
      backend=$2
      shift 2
      ;;
    --no-exact-control)
      include_exact=0
      controls_explicit=1
      shift
      ;;
    --no-uncapped-control)
      include_uncapped=0
      controls_explicit=1
      shift
      ;;
    --split-fp)
      split_fp=1
      shift
      ;;
    --no-split-fp)
      split_fp=0
      shift
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    --)
      shift
      extra_args=("$@")
      break
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
done

[[ -n $solver ]] || die '--solver is required'
[[ -x $solver ]] || die "solver is not executable: $solver"
if [[ -n $list ]]; then
  [[ -z $corpus ]] || die '--corpus and --list are mutually exclusive'
  [[ -f $list ]] || die "query list is not a file: $list"
  list_dir=$(cd "$(dirname "$list")" && pwd -P) ||
    die "cannot resolve query-list directory: $list"
  list=$list_dir/$(basename "$list")
else
  [[ -n $corpus ]] || die 'one of --corpus or --list is required'
  [[ -d $corpus ]] || die "corpus is not a directory: $corpus"
  corpus=$(cd "$corpus" && pwd -P) || die "cannot resolve corpus: $corpus"
fi
[[ $repetitions =~ ^[1-9][0-9]*$ ]] || die '--repetitions must be positive'
[[ $timeout_seconds =~ ^[1-9][0-9]*([.][0-9]+)?$ ]] ||
  die '--timeout must be positive'
[[ $width =~ ^[1-9][0-9]*$ ]] || die '--width must be positive'
case "$backend" in
  minisat|cadical|default) ;;
  *) die '--backend must be minisat, cadical, or default' ;;
esac

command -v timeout >/dev/null 2>&1 || die 'GNU timeout is required'
command -v sha256sum >/dev/null 2>&1 || die 'sha256sum is required'
time_bin=/usr/bin/time
[[ -x $time_bin ]] || die '/usr/bin/time is required'

limits=()
profiles=()
custom_variant_names=()
declare -A custom_variant_flags=()
custom_mode=0
if ((${#custom_variant_specs[@]} > 0)); then
  custom_mode=1
  [[ -z $profiles_csv ]] || die '--variant and --profiles are mutually exclusive'
  ((limits_explicit == 0)) || die '--variant and --limits are mutually exclusive'
  ((controls_explicit == 0)) ||
    die '--variant cannot be combined with built-in control switches'
  ((width_explicit == 0)) ||
    die '--variant does not imply --width; put the width in common arguments'

  for spec in "${custom_variant_specs[@]}"; do
    [[ $spec == *:* ]] || die "--variant needs NAME:FLAGS: $spec"
    name=${spec%%:*}
    flags=${spec#*:}
    [[ $name =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]] ||
      die "invalid variant name: $name"
    for old in "${custom_variant_names[@]}"; do
      [[ $old != "$name" ]] || die "duplicate variant name: $name"
    done
    [[ $flags != *$'\t'* && $flags != *$'\n'* ]] ||
      die "variant flags cannot contain tabs or newlines: $name"
    custom_variant_names+=("$name")
    custom_variant_flags["$name"]=$flags
  done
elif [[ -n $profiles_csv ]]; then
  ((limits_explicit == 0)) || die '--profiles and --limits are mutually exclusive'
  IFS=, read -r -a requested_profiles <<< "$profiles_csv"
  for profile in "${requested_profiles[@]}"; do
    [[ $profile =~ ^[a-z0-9][a-z0-9-]*$ ]] ||
      die "invalid profile name: $profile"
    duplicate=0
    for old in "${profiles[@]}"; do
      [[ $old == "$profile" ]] && duplicate=1
    done
    ((duplicate == 0)) && profiles+=("$profile")
  done
  ((${#profiles[@]} > 0)) || die '--profiles supplied no names'
else
  IFS=, read -r -a requested_limits <<< "$limits_csv"
  for limit in "${requested_limits[@]}"; do
    [[ $limit =~ ^[1-9][0-9]*$ ]] ||
      die "every value limit must be a positive integer: $limit"
    duplicate=0
    for old in "${limits[@]}"; do
      [[ $old == "$limit" ]] && duplicate=1
    done
    ((duplicate == 0)) && limits+=("$limit")
  done
  ((${#limits[@]} > 0)) || die '--limits supplied no values'
fi

queries=()
if [[ -n $list ]]; then
  list_dir=$(dirname "$list")
  declare -A seen_queries=()
  while IFS= read -r query || [[ -n $query ]]; do
    query=${query%$'\r'}
    [[ $query =~ ^[[:space:]]*$ ]] && continue
    [[ $query =~ ^[[:space:]]*# ]] && continue
    [[ $query != *$'\t'* ]] || die 'query-list paths cannot contain tabs'
    if [[ $query != /* ]]; then
      query=$list_dir/$query
    fi
    [[ -f $query ]] || die "query-list entry is not a file: $query"
    query_dir=$(cd "$(dirname "$query")" && pwd -P) ||
      die "cannot resolve query-list entry: $query"
    query=$query_dir/$(basename "$query")
    [[ -z ${seen_queries["$query"]+present} ]] ||
      die "duplicate query-list entry: $query"
    seen_queries["$query"]=1
    queries+=("$query")
  done < "$list"
  ((${#queries[@]} > 0)) || die "no query paths found in $list"
else
  mapfile -d '' queries < <(
    find -L "$corpus" -maxdepth 1 -type f -name '*.smt2' -print0 | sort -z)
  ((${#queries[@]} > 0)) || die "no *.smt2 files found in $corpus"
fi

if [[ -z $output ]]; then
  output=$(mktemp -d /tmp/stp-bv-refinement.XXXXXX) ||
    die 'could not create result directory'
else
  [[ ! -e $output ]] || die "refusing to overwrite existing path: $output"
  mkdir -p "$output" || die "could not create output directory: $output"
fi
mkdir -p "$output/logs" || die 'could not create log directory'

runs_tsv=$output/runs.tsv
records_tsv=$output/records.tsv
summary_tsv=$output/summary.tsv
comparisons_tsv=$output/comparisons.tsv
comparison_summary_tsv=$output/comparison-summary.tsv
disagreements_tsv=$output/disagreements.tsv
metadata=$output/metadata.txt
corpus_hashes=$output/corpus.sha256

printf '%s\n' \
  $'repetition\tschedule\tvariant\tclass\tdriver\tquery\tverdict\tstatus\texit_code\twall_seconds\tmax_rss_kb\tcandidates_divmod\tabstracted_divmod\trefinement_rounds\tblocking_lemmas\tschema_lemmas\texact_escalations\texact_mult\texact_divmod\trecords\trecord_blocking_sum\trecord_blocking_max\tpaired_records\tpaired_blocking_sum\tunpaired_divmod_blocking_sum\trecord_blocking_clauses\trecord_blocking_literals\trecord_exact_clauses\trecord_exact_variables\trecord_exact_microseconds\taggregate_exact_clauses\taggregate_exact_variables\taggregate_exact_microseconds\taggregate_schema_clauses\taggregate_schema_variables\taggregate_schema_microseconds\tlog' \
  > "$runs_tsv"
printf '%s\n' \
  $'repetition\tvariant\tclass\tdriver\tquery\trecord\tnode\tkind\twidth\tstate\tblocking\tschemas\texact\texact_bits\tallowance\tpaired\tpair_full\tblocking_clauses\tblocking_literals\texact_clauses\texact_variables\texact_microseconds\tlog' \
  > "$records_tsv"

common_args=(--SMTLIB2 --incremental=off --cnf-auto-threshold=0 -t)
case "$backend" in
  minisat) common_args+=(--minisat) ;;
  cadical) common_args+=(--cadical) ;;
esac

variants=()
reference_variant=
if ((custom_mode)); then
  variants=("${custom_variant_names[@]}")
  reference_variant=${variants[0]}
elif ((include_exact)); then
  variants+=(exact)
fi
if ((custom_mode)); then
  :
elif ((${#profiles[@]} > 0)); then
  for profile in "${profiles[@]}"; do
    variants+=("profile-$profile")
  done
  reference_variant=profile-${profiles[0]}
else
  if ((include_uncapped)); then
    variants+=(uncapped)
    reference_variant=uncapped
  fi
  for limit in "${limits[@]}"; do
    variants+=("cap$limit")
  done
fi
((${#variants[@]} > 0)) || die 'all variants were disabled'

variant_args()
{
  local variant=$1
  VARIANT_ARGS=()
  if ((custom_mode)); then
    local flags=${custom_variant_flags["$variant"]}
    if [[ -n $flags ]]; then
      read -r -a VARIANT_ARGS <<< "$flags"
    fi
    return
  fi

  if [[ $variant == exact ]]; then
    VARIANT_ARGS+=(--bv-eq-abstraction=0 --bv-term-abstraction=0)
    return
  fi

  VARIANT_ARGS+=(--bv-eq-abstraction=1 --bv-term-abstraction=1)
  VARIANT_ARGS+=("--bv-abstraction-width=$width")
  if [[ $variant == profile-* ]]; then
    VARIANT_ARGS+=("--bv-term-abstraction-profile=${variant#profile-}")
    return
  fi

  VARIANT_ARGS+=(--bv-term-abstraction-profile=qualified)
  if [[ $variant == cap* ]]; then
    VARIANT_ARGS+=("--bv-term-abstraction-divmod-value-limit=${variant#cap}")
  fi
}

# Fail before a long corpus run if this binary lacks an option or backend.
smoke=$output/smoke.smt2
printf '%s\n' '(set-logic QF_BV)' '(check-sat)' > "$smoke"
for variant in "${variants[@]}"; do
  variant_args "$variant"
  smoke_log=$output/smoke-$variant.log
  timeout 10 "$solver" "${common_args[@]}" "${VARIANT_ARGS[@]}" \
    "${extra_args[@]}" "$smoke" > "$smoke_log" 2>&1
  smoke_exit=$?
  if ((smoke_exit != 0)) ||
     ! awk '/^(sat|unsat)$/ { found=1 } END { exit !found }' "$smoke_log"; then
    printf 'option smoke test failed for %s; output follows:\n' "$variant" >&2
    sed -n '1,160p' "$smoke_log" >&2
    die 'solver/options are not usable'
  fi
done
rm -f "$smoke" "$output"/smoke-*.log

{
  printf 'started_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf 'solver=%s\n' "$solver"
  if [[ -n $list ]]; then
    printf 'input_kind=list\n'
    printf 'input=%s\n' "$list"
    printf 'input_sha256=%s\n' "$(sha256sum "$list" | awk '{print $1}')"
  else
    printf 'input_kind=corpus\n'
    printf 'input=%s\n' "$corpus"
  fi
  printf 'query_count=%d\n' "${#queries[@]}"
  printf 'repetitions=%s\n' "$repetitions"
  printf 'timeout_seconds=%s\n' "$timeout_seconds"
  printf 'width=%s\n' "$width"
  printf 'backend=%s\n' "$backend"
  printf 'split_fp=%s\n' "$split_fp"
  if ((custom_mode)); then
    printf 'variant_mode=custom\n'
  else
    printf 'variant_mode=builtin\n'
  fi
  printf 'variants=%s\n' "${variants[*]}"
  printf 'profiles=%s\n' "${profiles[*]:-none}"
  printf 'comparison_reference=%s\n' "${reference_variant:-none}"
  for variant in "${variants[@]}"; do
    variant_args "$variant"
    printf 'variant_%s_args=' "$variant"
    if ((${#VARIANT_ARGS[@]} > 0)); then
      printf ' %q' "${VARIANT_ARGS[@]}"
    fi
    printf '\n'
  done
  printf 'common_args='; printf ' %q' "${common_args[@]}"; printf '\n'
  printf 'extra_args='; printf ' %q' "${extra_args[@]}"; printf '\n'
  printf 'solver_sha256=%s\n' "$(sha256sum "$solver" | awk '{print $1}')"
  printf 'harness_sha256=%s\n' \
    "$(sha256sum "${BASH_SOURCE[0]}" | awk '{print $1}')"
  printf 'host=%s\n' "$(uname -a)"
  "$solver" --version 2>&1 | sed 's/^/solver_version=/'
} > "$metadata"

for query_index in "${!queries[@]}"; do
  query=${queries[query_index]}
  if [[ -n $list ]]; then
    query_key=$query
  else
    query_key=$(basename "$query")
  fi
  printf '%s  %s\n' "$(sha256sum "$query" | awk '{print $1}')" \
    "$query_key"
done > "$corpus_hashes"
printf 'corpus_manifest_sha256=%s\n' \
  "$(sha256sum "$corpus_hashes" | awk '{print $1}')" >> "$metadata"

total_runs=$((repetitions * ${#queries[@]} * ${#variants[@]}))
run_number=0
errors=0

for ((rep = 1; rep <= repetitions; ++rep)); do
  for ((query_index = 0; query_index < ${#queries[@]}; ++query_index)); do
    query=${queries[query_index]}
    query_name=$(basename "$query")
    if [[ -n $list ]]; then
      query_key=$query
    else
      query_key=$query_name
    fi
    driver=$(sed -E 's/_[0-9]+[.]smt2$//; s/[.]smt2$//' <<< "$query_name")
    if ((split_fp == 0)); then
      query_class=all
    elif grep -q 'fp[.]' "$query"; then
      query_class=fp
    else
      query_class=bv
    fi

    rotation=$(((query_index + rep - 1) % ${#variants[@]}))
    for ((schedule = 0; schedule < ${#variants[@]}; ++schedule)); do
      variant_index=$(((rotation + schedule) % ${#variants[@]}))
      variant=${variants[variant_index]}
      variant_args "$variant"

      ((run_number++))
      run_id=$(printf 'r%02d-q%05d-s%02d-%s' "$rep" "$query_index" \
                      "$schedule" "$variant")
      log=$output/logs/$run_id.log
      timing=$output/logs/$run_id.time
      relative_log=logs/$run_id.log

      printf '[%d/%d] rep=%d query=%s variant=%s\n' \
        "$run_number" "$total_runs" "$rep" "$query_name" "$variant" >&2

      # --quiet suppresses GNU time's "Command exited ..." line. Without it,
      # a timeout puts that prose on the first line of the timing file and a
      # naïve read loses both elapsed time and RSS for the censored run.
      "$time_bin" --quiet -f $'%e\t%M' -o "$timing" \
        timeout --signal=TERM --kill-after=2 "${timeout_seconds}s" \
        "$solver" "${common_args[@]}" "${VARIANT_ARGS[@]}" \
        "${extra_args[@]}" "$query" > "$log" 2>&1
      exit_code=$?

      wall_seconds=$timeout_seconds
      max_rss_kb=0
      if [[ -s $timing ]]; then
        timing_line=$(awk -F '\t' '
          $1 ~ /^[0-9]+([.][0-9]+)?$/ && $2 ~ /^[0-9]+$/ { value=$0 }
          END { print value }' "$timing")
        if [[ -n $timing_line ]]; then
          IFS=$'\t' read -r wall_seconds max_rss_kb <<< "$timing_line"
        fi
      fi
      rm -f "$timing"

      verdict=$(awk '/^(sat|unsat|unknown)$/ { print; exit }' "$log")
      if ((exit_code == 124 || exit_code == 137)); then
        status=timeout
        verdict=
      elif ((exit_code != 0)); then
        status=error
        ((errors++))
      elif [[ $verdict == sat || $verdict == unsat ]]; then
        status=ok
      elif [[ $verdict == unknown ]]; then
        status=unknown
      else
        status=no-verdict
        ((errors++))
      fi

      coverage=$(awk '
        /^Abstraction coverage / {
          for (i = 1; i <= NF; ++i)
            if ($i ~ /^divmod=/) {
              sub(/^divmod=/, "", $i); split($i, n, "->");
              print n[1] "\t" n[2]; exit
            }
        }' "$log")
      candidates_divmod=0
      abstracted_divmod=0
      if [[ -n $coverage ]]; then
        IFS=$'\t' read -r candidates_divmod abstracted_divmod <<< "$coverage"
      fi

      refinement=$(awk '
        /^Abstraction refinement:/ {
          for (i = 3; i <= NF; ++i) {
            split($i, kv, "="); v[kv[1]] = kv[2]
          }
          printf "%s\t%s\t%s\t%s\t%s\t%s\n", v["rounds"],
                 v["blocking"], v["schema"], v["exact"],
                 v["exact-mult"], v["exact-divmod"]
          exit
        }' "$log")
      refinement_rounds=0
      blocking_lemmas=0
      schema_lemmas=0
      exact_escalations=0
      exact_mult=0
      exact_divmod=0
      if [[ -n $refinement ]]; then
        IFS=$'\t' read -r refinement_rounds blocking_lemmas schema_lemmas \
          exact_escalations exact_mult exact_divmod <<< "$refinement"
      fi

      escalation_cost=$(awk '
        /^Abstraction circuit cost:/ {
          for (i = 4; i <= NF; ++i) {
            split($i, kv, "="); v[kv[1]] = kv[2]
          }
          printf "%s\t%s\t%s\n", v["clauses"], v["variables"],
                 v["microseconds"]
          exit
        }' "$log")
      aggregate_exact_clauses=0
      aggregate_exact_variables=0
      aggregate_exact_microseconds=0
      if [[ -n $escalation_cost ]]; then
        IFS=$'\t' read -r aggregate_exact_clauses \
          aggregate_exact_variables aggregate_exact_microseconds \
          <<< "$escalation_cost"
      fi

      # The other half of what a refinement costs. A variant is usually a
      # different set of schema families, so this is the column the campaign
      # exists to compare; the line above covers only what a record spent
      # after giving up on abstracting it.
      schema_cost=$(awk '
        /^Abstraction schema cost:/ {
          for (i = 4; i <= NF; ++i) {
            split($i, kv, "="); v[kv[1]] = kv[2]
          }
          printf "%s\t%s\t%s\n", v["clauses"], v["variables"],
                 v["microseconds"]
          exit
        }' "$log")
      aggregate_schema_clauses=0
      aggregate_schema_variables=0
      aggregate_schema_microseconds=0
      if [[ -n $schema_cost ]]; then
        IFS=$'\t' read -r aggregate_schema_clauses \
          aggregate_schema_variables aggregate_schema_microseconds \
          <<< "$schema_cost"
      fi

      record_stats=$(awk '
        BEGIN {
          count=0; sum=0; max=0; paired=0; pairblocks=0; singlediv=0
          blockclauses=0; blockliterals=0; exactclauses=0; exactvars=0
          exactus=0
        }
        /^BV abstraction record:/ {
          delete v
          for (i = 4; i <= NF; ++i) {
            split($i, kv, "="); v[kv[1]] = kv[2]
          }
          ++count; sum += v["blocking"]
          if (v["blocking"] > max) max = v["blocking"]
          if (v["paired"] == 1) {
            ++paired; pairblocks += v["blocking"]
          } else if (v["kind"] == "BVDIV" || v["kind"] == "BVMOD")
            singlediv += v["blocking"]
          blockclauses += v["blocking-clauses"]
          blockliterals += v["blocking-literals"]
          exactclauses += v["exact-clauses"]
          exactvars += v["exact-vars"]
          exactus += v["exact-us"]
        }
        END {
          printf "%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n",
                 count, sum, max, paired, pairblocks, singlediv,
                 blockclauses, blockliterals, exactclauses, exactvars,
                 exactus
        }' "$log")
      IFS=$'\t' read -r record_count record_blocking_sum record_blocking_max \
        paired_records paired_blocking_sum unpaired_divmod_blocking_sum \
        record_blocking_clauses record_blocking_literals \
        record_exact_clauses record_exact_variables record_exact_microseconds \
        <<< "$record_stats"

      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$rep" "$schedule" "$variant" "$query_class" "$driver" \
        "$query_key" "$verdict" "$status" "$exit_code" "$wall_seconds" \
        "$max_rss_kb" "$candidates_divmod" "$abstracted_divmod" \
        "$refinement_rounds" "$blocking_lemmas" "$schema_lemmas" \
        "$exact_escalations" "$exact_mult" "$exact_divmod" "$record_count" \
        "$record_blocking_sum" "$record_blocking_max" "$paired_records" \
        "$paired_blocking_sum" "$unpaired_divmod_blocking_sum" \
        "$record_blocking_clauses" "$record_blocking_literals" \
        "$record_exact_clauses" "$record_exact_variables" \
        "$record_exact_microseconds" "$aggregate_exact_clauses" \
        "$aggregate_exact_variables" "$aggregate_exact_microseconds" \
        "$aggregate_schema_clauses" "$aggregate_schema_variables" \
        "$aggregate_schema_microseconds" "$relative_log" \
        >> "$runs_tsv"

      awk -v OFS='\t' -v rep="$rep" -v variant="$variant" \
        -v class="$query_class" -v driver="$driver" -v query="$query_key" \
        -v log_path="$relative_log" '
        /^BV abstraction record:/ {
          delete v
          for (i = 4; i <= NF; ++i) {
            split($i, kv, "="); v[kv[1]] = kv[2]
          }
          print rep, variant, class, driver, query, v["record"], v["node"],
                v["kind"], v["width"], v["state"], v["blocking"],
                v["schemas"], v["exact"], v["exact-bits"], v["allowance"],
                v["paired"], v["pair-full"],
                v["blocking-clauses"], v["blocking-literals"],
                v["exact-clauses"], v["exact-vars"], v["exact-us"], log_path
        }' "$log" >> "$records_tsv"
    done
  done
done

awk -F '\t' -v OFS='\t' '
  NR == 1 { next }
  {
    for (group = 0; group < 2; ++group) {
      driver = group == 0 ? $5 : "ALL"
      key=$3 SUBSEP $4 SUBSEP driver
      runs[key]++
      wall[key]+=$10
      rss[key]+=$11
      blocks[key]+=$15
      schemas[key]+=$16
      exact[key]+=$17
      pairblocks[key]+=$24
      singlediv[key]+=$25
      blockclauses[key]+=$26
      blockliterals[key]+=$27
      exactclauses[key]+=$28
      exactvars[key]+=$29
      exactus[key]+=$30
      aggregateexactclauses[key]+=$31
      aggregateexactvars[key]+=$32
      aggregateexactus[key]+=$33
      aggregateschemaclauses[key]+=$34
      aggregateschemavars[key]+=$35
      aggregateschemaus[key]+=$36
      if ($8 == "ok") verdicts[key]++
      else if ($8 == "timeout") timeouts[key]++
      else if ($8 == "unknown") unknowns[key]++
      else failures[key]++
    }
  }
  END {
    print "variant", "class", "driver", "runs", "verdicts", "timeouts",
          "unknown", "failures", "wall_seconds", "mean_rss_kb",
          "blocking_lemmas", "schema_lemmas", "exact_escalations",
          "paired_blocking", "unpaired_divmod_blocking",
          "record_blocking_clauses", "record_blocking_literals",
          "record_exact_clauses", "record_exact_variables",
          "record_exact_microseconds", "aggregate_exact_clauses",
          "aggregate_exact_variables", "aggregate_exact_microseconds",
          "aggregate_schema_clauses", "aggregate_schema_variables",
          "aggregate_schema_microseconds"
    for (key in runs) {
      split(key, k, SUBSEP)
      printf "%s\t%s\t%s\t%d\t%d\t%d\t%d\t%d\t%.6f\t%.1f\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n",
             k[1], k[2], k[3], runs[key], verdicts[key], timeouts[key],
             unknowns[key], failures[key], wall[key], rss[key]/runs[key],
             blocks[key], schemas[key], exact[key], pairblocks[key],
             singlediv[key], blockclauses[key], blockliterals[key],
             exactclauses[key], exactvars[key], exactus[key],
             aggregateexactclauses[key], aggregateexactvars[key],
             aggregateexactus[key], aggregateschemaclauses[key],
             aggregateschemavars[key], aggregateschemaus[key]
    }
  }' "$runs_tsv" | { IFS= read -r header; printf '%s\n' "$header";
                      sort -t $'\t' -k1,1 -k2,2 -k3,3; } > "$summary_tsv"

# A blocked campaign is most useful as a matched experiment: each variant's
# row sits beside the reference row for the same repetition and query. Preserve
# that join explicitly so an aggregate regression can be separated from
# scheduler noise and from a handful of large outliers without scraping logs.
printf '%s\n' \
  $'repetition\tclass\tdriver\tquery\tvariant\treference_status\tvariant_status\treference_wall_seconds\tvariant_wall_seconds\tdelta_seconds\twall_ratio\treference_blocking\tvariant_blocking\treference_exact\tvariant_exact' \
  > "$comparisons_tsv"
if [[ -n $reference_variant ]]; then
  awk -F '\t' -v OFS='\t' -v reference_variant="$reference_variant" '
    NR == 1 { next }
    {
      key=$1 SUBSEP $6
      item=key SUBSEP $3
      class[key]=$4; driver[key]=$5
      status[item]=$8; wall[item]=$10
      blocking[item]=$15; exact[item]=$17
      if ($3 != reference_variant) seen[item]=1
    }
    END {
      for (item in seen) {
        split(item, p, SUBSEP)
        key=p[1] SUBSEP p[2]
        variant=p[3]
        reference=key SUBSEP reference_variant
        if (!(reference in status)) continue
        delta=wall[item]-wall[reference]
        ratio=wall[reference] == 0 ? 0 : wall[item]/wall[reference]
        printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%.6f\t%.6f\t%.6f\t%.6f\t%d\t%d\t%d\t%d\n",
               p[1], class[key], driver[key], p[2], variant,
               status[reference], status[item], wall[reference], wall[item],
               delta, ratio, blocking[reference], blocking[item],
               exact[reference], exact[item]
      }
    }' "$runs_tsv" | sort -t $'\t' -k1,1n -k2,2 -k3,3 -k4,4 -k5,5 \
    >> "$comparisons_tsv"
fi

awk -F '\t' -v OFS='\t' '
  NR == 1 { next }
  {
    for (group = 0; group < 2; ++group) {
      driver = group == 0 ? $3 : "ALL"
      key=$5 SUBSEP $2 SUBSEP driver
      comparisons[key]++
      if ($6 == "ok" && $7 == "ok") {
        comparable[key]++
        delta[key]+=$10
        if ($10 < 0) wins[key]++
        else if ($10 > 0) losses[key]++
        else ties[key]++
      } else if ($6 != $7)
        status_mismatches[key]++
    }
  }
  END {
    print "variant", "class", "driver", "comparisons", "comparable",
          "wins", "ties", "losses", "status_mismatches", "delta_seconds"
    for (key in comparisons) {
      split(key, k, SUBSEP)
      printf "%s\t%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%.6f\n",
             k[1], k[2], k[3], comparisons[key], comparable[key],
             wins[key], ties[key], losses[key], status_mismatches[key],
             delta[key]
    }
  }' "$comparisons_tsv" | { IFS= read -r header; printf '%s\n' "$header";
      sort -t $'\t' -k1,1 -k2,2 -k3,3; } > "$comparison_summary_tsv"

awk -F '\t' -v OFS='\t' '
  NR == 1 { next }
  {
    key=$1 SUBSEP $6
    if ($7 == "sat" || $7 == "unsat") {
      if (!(key in answer)) answer[key]=$7
      else if (answer[key] != $7)
        bad[key]=answer[key] "," $7
    }
  }
  END {
    print "repetition", "query", "answers"
    for (key in bad) {
      split(key, k, SUBSEP); print k[1], k[2], bad[key]
    }
  }' "$runs_tsv" > "$disagreements_tsv"

printf 'finished_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$metadata"

printf 'Results: %s\n' "$output" >&2
printf 'Summary: %s\n' "$summary_tsv" >&2
if ((errors != 0)); then
  printf '%d non-timeout runs failed or returned no verdict\n' "$errors" >&2
  exit 1
fi
if (( $(wc -l < "$disagreements_tsv") > 1 )); then
  printf 'answer disagreements found: %s\n' "$disagreements_tsv" >&2
  exit 1
fi
