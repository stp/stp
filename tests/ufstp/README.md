# UF acceptance harnesses

These deterministic harnesses generate their SMT-LIB corpus on demand, check
every verdict, and can write machine-readable evidence whose corpus digest
pins the exact generated inputs.

`performance.py` exercises durable lowering, `define-fun` reuse, nested
`let`, identical-query reuse, pop scoping, and encoding-epoch rebuilds in
both batch and persistent modes, plus one family each for floating-point
congruence and rounding-mode exhaustion. Those two are separate rows because
the sorts do not scale like the bit-vector ones: a float actual reaches the
checker through a pack/unpack boundary, and the query's own `(= a b)` over
floats is `FP_SMT_EQ`, which equality propagation cannot substitute through.
It is an answer-checked trend benchmark, not a wall-clock threshold:

```sh
python3 tests/ufstp/performance.py \
  --stp build/stp --scales 16,64 --repeats 2 \
  --evidence-out /tmp/uf-performance.json
```

`differential_fuzz.py` covers nested congruence, non-injectivity, Boolean
predicates, interpreted equality, arrays as actuals, declaration separation,
compound-result liveness, and RoundingMode and FloatingPoint in both
signature positions --
including result tuples that exhaust all five rounding modes (which forces an
introduced result symbol to be pinned rather than merely constrained) and
NaN-against-the-zeros floating-point tuples (which tell a semantic quotient
from a convenient normalisation). Every case runs in both STP modes and
through each named reference solver:

```sh
python3 tests/ufstp/differential_fuzz.py \
  --stp build/stp \
  --reference z3=/usr/bin/z3 \
  --reference cvc5=/usr/bin/cvc5 \
  --seeds 240 --evidence-out /tmp/uf-differential.json
```

References are repeatable. Z3 and CVC5 command-line forms are recognized;
other solvers are invoked as `COMMAND input.smt2`. A separately built peer
STP can also be used as `--reference "peer=/path/to/stp
--uninterpreted-functions"`.

For CI without external solvers, `scripts/fuzz/uf-differential-fuzz.py`
provides an independent local oracle: the generator eagerly Ackermannizes
each UF instance and submits that UF-free formula to STP's classic solver,
then compares it with both lazy UF adapters. It also compares complete
push/pop verdict sequences.
