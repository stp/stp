#!/usr/bin/env bash

# A deterministic stand-in for the benchmark harness regression. It accepts
# the harness's ordinary STP arguments, reads only the final query path, and
# emits the same machine-readable telemetry as a completed abstraction run.

set -u

if (($# == 1)) && [[ $1 == --version ]]; then
  printf '%s\n' 'STP benchmark harness fake solver 1'
  exit 0
fi

(($# > 0)) || exit 2
query=${!#}
[[ -f $query ]] || exit 2

# The harness creates an unmarked smoke query before the real population.
if ! grep -q '^; HARNESS_COST=1$' "$query"; then
  printf '%s\n' sat
  exit 0
fi

verdict=sat
grep -q '^; HARNESS_VERDICT=unsat$' "$query" && verdict=unsat

# A multiplication that escalated, and a BVDIV/BVMOD pair that took the
# full-width recomposition between them. The pair is what makes the two cost
# lines disagree on purpose: its circuit belongs to two records rather than
# either, so it is charged to the totals and to neither record's own fields.
# Without a pair in the fixture the harness check could assert that the
# aggregate equals the per-record sum and pass, which it did.
printf '%s\n' \
  'BV abstraction record: record=0 node=7 kind=BVMULT width=64 state=exact blocking=1 schemas=0 exact=1 exact-bits=64 allowance=1 paired=0 pair-full=0 blocking-clauses=64 blocking-literals=128 exact-clauses=123 exact-vars=45 exact-us=67' \
  'BV abstraction record: record=1 node=9 kind=BVDIV width=64 state=open blocking=0 schemas=1 exact=0 exact-bits=0 allowance=1 paired=1 pair-full=1 blocking-clauses=0 blocking-literals=0 exact-clauses=0 exact-vars=0 exact-us=0' \
  'BV abstraction record: record=2 node=11 kind=BVMOD width=64 state=open blocking=0 schemas=1 exact=0 exact-bits=0 allowance=1 paired=1 pair-full=1 blocking-clauses=0 blocking-literals=0 exact-clauses=0 exact-vars=0 exact-us=0' \
  'Abstraction coverage (candidates -> abstracted): eq=0->0 compare=0->0 ite=0->0 plus=0->0 mult=1->1 divmod=2->2' \
  'Abstraction refinement: rounds=4 blocking=1 schema=2 exact=1 exact-mult=1 exact-divmod=0' \
  'Abstraction circuit cost: clauses=1123 variables=1045 microseconds=1067' \
  'Abstraction schema cost: clauses=500 variables=60 microseconds=70' \
  'Abstraction schemas by group: base=0 divrem-full=1' \
  "$verdict"
