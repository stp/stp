# propagator_bench

How fast are STP's propagators, and how much do they deduce?

The tool times one transfer function at a time, over random cases at a chosen
bit-width and a chosen density of known input bits, and reports operations per
second alongside a verdict on whether the propagator is *maximally precise* --
whether it deduces everything that follows from what it was given.

It covers the three abstract domains STP propagates over:

| domain | code | direction |
| --- | --- | --- |
| `cbitp` | `simplifier::constantBitP`, the `bv*BothWays` transfer functions | both ways |
| `interval` | `stp::UnsignedIntervalAnalysis::dispatchToTransferFunctions` | bottom up |
| `valueset` | `stp::ValueSetAnalysis::dispatchToTransferFunctions` | bottom up |

## Building and running

It is one of the extra tools:

```sh
cmake -DBUILD_EXTRA_TOOLS=ON -DCMAKE_BUILD_TYPE=Release ..
make propagator_bench
```

Build Release. A Debug build measures the assertions, not the propagators.

```sh
# Everything, into an HTML report (tens of minutes).
./propagator_bench --html propagator-bench.html --csv propagator-bench.csv

# One question, quickly.
./propagator_bench --domains cbitp --ops bvsgt --widths 64 --probs 50 \
                   --directions bottom-up
```

`--list` shows the operations and which domains implement them, `--help` the
rest of the options.

## What a row means

> cbitp, bvsgt, bottom-up, 64 bit, 50% fixed: 40.7M ops/sec, 0.19 bits, precise

* **direction** is what was *seeded*, not what the code can deduce. The
  constant-bit transfer functions all propagate in both directions; the
  interval and value-set analyses only ever compute a node's domain from its
  children's, so they only have bottom-up rows.
  * `bottom-up` -- children partially known, result unknown.
  * `top-down` -- result partially known, children unknown.
  * `both-ways` -- everything partially known.
* **input** is how much was known going in: for `cbitp` and `interval`, the
  percentage of bits fixed; for `valueset`, the number of values in each
  input set.
* **ops/sec** is the median of `--repeats` timed runs. The propagators mutate
  their arguments, so every run works on a fresh copy, made outside the timed
  region.
* **bits** is what the call deduced, in bits: newly fixed bits for `cbitp`,
  and the width less the log of the domain's size for `interval` and
  `valueset`. It is the thing the ops/sec figure buys.
* **precise** is the precision verdict, described below.

Every case is built by drawing a concrete solution, evaluating it with STP's
own constant evaluator, and then forgetting bits of it. So no case is
contradictory, no propagator can short-circuit on a conflict, and the
solution gives a free soundness check: a propagator that excludes it is
reported as unsound rather than fast.

## The precision verdict

*Maximally precise* means: given these inputs, no sound propagator could have
deduced more. It is checked two ways.

**Exhaustively, at a small width** (`--precision-width`, default 4, lowered
automatically when the enumeration would be too large). Every combination of
input domains is enumerated -- all ternary patterns for `cbitp`, all
intervals for `interval`, all subsets for `valueset` -- and for each one the
ideal answer is brute-forced from the operation's truth table. The row says
`12/6561 cases` and what share of the deducible bits were found. A propagator
that is precise at width 4 is not proven precise at width 64, which is why
the width is printed.

**Against the SAT solver, at the benchmarked width** (`--sat-check N`). The
existing `maxPrecision()` in `ConstantBitP_MaxPrecision.cpp` computes the join
of every solution by repeatedly calling the SAT solver, which is exact at any
width but thousands of times slower than the propagator; `--sat-budget`
caps how long a row may spend on it. This one is `cbitp` only, and skips
`extract` and the two extends, whose structural children can't be turned into
plain SAT variables.

A row is `yes` only when both checks that ran agree, `no` when either found
something more to deduce, and `unsound` when a real solution was excluded --
which would be a bug in the propagator, not a precision result.

## Caveats worth knowing before quoting a number

* **The machine matters.** These are absolute timings; on a loaded box they
  are an upper bound on cost. For an A/B comparison of two implementations,
  interleave the two in the same process rather than comparing two runs.
* **Shift amounts are biased.** A uniformly random 64-bit shift amount is out
  of range almost every time, so half of them are drawn from `[0, width)`
  instead. `--no-shift-bias` turns that off.
* **Divisors are not biased**, so a random 64-bit division is usually a
  division by a huge number.
* **n-ary operations are timed at `--arity` children** (default 2), which
  understates `bvand` and `bvadd` as the solver actually sees them.
* **`valueset` rows go null often.** Two 4-element sets multiply out to 16
  possible results, past the 12 the domain can hold, so the analysis widens to
  "unknown" and the deduced bits drop to zero. That is the domain working as
  designed, not a measurement problem.
* **`valueset` timings are noisy.** Every call evaluates through the constant
  evaluator, which interns nodes, so the cost drifts upwards as the node table
  fills: the same configuration has come out anywhere between 89k and 139k
  calls a second in the same process. Take a difference of less than about
  50% there as nothing at all, and compare two implementations by
  alternating them, not by comparing two runs.
