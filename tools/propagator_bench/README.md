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

It is one of the extra tools, and it needs a build with CryptoMiniSat --
without one the target is not created at all and the configure step says so:

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

# Is the propagator deducing more than the bit-blasted encoding would?
./propagator_bench --domains cbitp --widths 16 --probs 50 --no-precision \
                   --bcp-check 200
```

`--list` shows the operations and which domains implement them, `--help` the
rest of the options.

## What a row means

Output is a fixed-width table with the columns `op`, `direction`, `width`,
`input`, `ops/sec`, `ns/call`, `bits`, `precise` and `detail`. Reading one row:
`cbitp` on `bvsgt`, seeded `bottom-up`, at 64 bits with 50% of the input bits
fixed, deducing 0.19 bits per call.

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

A row is `yes` only when the exhaustive check ran and found nothing more to
deduce, and any SAT check that also ran agreed; `no` when either found
something more to deduce; and `unsound` when a real solution was excluded --
which would be a bug in the propagator, not a precision result. Without the
exhaustive check the column is `?`, whatever the SAT check said, because a
sampled check cannot establish precision on its own.

## Against the bit-blasted encoding

The precision verdict asks whether a *better* propagator could exist.
`--bcp-check N` asks the other question: whether this one is worth running at
all. STP bit-blasts to CNF and calls a SAT solver anyway, so a word-level
propagator only earns its keep by fixing bits that boolean constraint
propagation over the same circuit would not have fixed on its own.

The check encodes `op(children) = result` once per row, then per case asserts
the known bits as unit clauses and counts what comes out fixed at decision
level zero:

```
bvsrem  both-ways 16  50% fixed  ... vs bit-blasted: 0.69 vs 2.56 bits (3.7x)
bvand   both-ways 16  50% fixed  ... vs bit-blasted: 6.95 vs 6.95 bits (1.0x)
```

The multiplier is the propagator's bits over unit propagation's. `1.0x` means
the SAT solver would have found exactly the same bits without it, and most
operations report it: the bitwise ones, `eq`, `ite`, `concat`, `extract` and
both extends are identical, and `bvudiv` and `bvmul` are within a rounding
error. The signed division family is the one real margin -- `bvsrem` 3.7x,
`bvsmod` 3.5x, `bvsdiv` 2.6x -- with addition and the shifts at 1.1x to 1.35x.
`all new` is printed when unit propagation deduced nothing at all, so there is
no ratio to take.

`--cnf` picks how that CNF is generated -- `simple` (plain Tseitin), or the
five `cnf_effort` levels `very-low`, `low`, `medium` (STP's default), `high`,
`very-high`. The row reports the clause and variable counts, so the size of
the encoding and its propagation strength can be read together. For `bvand`
the setting changes the size by up to 2.1x and the deduced bits hardly at
all.

### Is the encoding arc-consistent?

`--bcp-check` samples, and every case it draws is built from a solution, so it
never asks whether propagation *detects a contradiction*. `--bcp-exhaustive W`
does both halves at a small width: every combination of fixed and unfixed bits
over the varying children and the result, contradictory ones included, against
a brute-forced ideal.

```
bvand   ... encoding arc-consistent w=4: yes (531441/531441 cases, 336960 contradictory)
bvadd   ... encoding arc-consistent w=3: NO (18851/19683 cases, 820 incomplete, 12 MISSED CONFLICTS)
```

`yes` requires all three: nothing left underived, no contradiction missed, and
nothing fixed that the ideal does not fix. Width 4 is 3^12 cases and takes
about 45 seconds; each step costs a fresh solver and a CNF load, so the cost
is 3^(children+result bits).

Operations whose bits are independent -- `bvand`, `bvor`, `bvxor`, `bvnot` --
come out arc-consistent under every `--cnf` setting. Ones with a carry chain
or a global relation -- `bvadd`, `bvmul`, `bvudiv`, `bvult` -- do not, which
is where the propagator earns its keep. `concat` and the two extends
need an even width, so choose W accordingly; `extract` only needs at least 2.

Both options need a CryptoMiniSat build (`-DUSE_CRYPTOMINISAT=ON`); they are
refused otherwise rather than quietly reporting nothing. It is much slower
per case than the propagator it measures -- a fresh solver and a full CNF
load each time -- so `--bcp-budget` caps it, and the reported per-case cost
in the `ns/call` column is the propagator's, never this.

Read the ratios at `--probs 50`. At 95% only a handful of bits per case are
unknown, so unit propagation's side of the comparison is a very small number
and the ratio swings widely with the seed.

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
