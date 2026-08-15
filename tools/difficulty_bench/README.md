# difficulty_bench

Is `DifficultyScore` a good estimate of the bit-blasted AIG size?

`DifficultyScore` predicts how many AIG AND-nodes the bit-blaster would build
for a formula, without building them. STP uses that prediction to decide
whether the size-increasing simplifications made the problem harder, and
reverts them if so. Every constant in `lib/Simplifier/DifficultyScore.cpp` was
fitted to the numbers this tool prints; re-run it after changing the
bit-blaster, and the estimate can be re-fitted rather than guessed at.

## What it measures

One operation at a time, built over *fresh symbols*, bit-blasted on its own
with `BBNodeManagerAIG`, and reported as `aigMgr->nObjs[AIG_OBJ_AND]`. Symbols
cost nothing to blast, so with fresh children the count is the marginal cost of
that one node — exactly what a per-node scorer has to charge for it.

Three things the numbers make visible that a reading of the bit-blaster does
not:

* **Operations are not symmetric in their operands.** `bvudiv c x` is linear in
  the *magnitude* of the constant dividend, whereas `bvudiv x c` is quadratic in
  the width; `bvand x c` is free.
* **The default multiplier is not Booth-recoded.** `multiplication_variant`
  defaults to 1, which is a plain shift-and-add array, so a multiply by a
  constant costs one add per *set bit*, not per run of set bits.
* **Floating point is dominated by a few operations.** `fp.sqrt` is cubic in
  the significand and `fp.rem` is exponential in the exponent width, so one of
  either can outweigh the rest of a benchmark.

Floating-point operations are lowered (`FpTotalise` then `FloatBlast`) before
being blasted, which is what the solver does. Each one runs in a forked child,
because an operation with no circuit at the format asked for — `fp.rem` at
binary128, `fp.roundToIntegral` at the smallest formats — calls `FatalError`.
Those rows report `n/a`.

The floating-point arithmetic is reported as the *marginal* cost of one more
operation in a chain: the tool prints a depth-2 chain and the depth-1 chain
under it, and the difference is what one operation costs. Measuring a lone
operation instead would fold in packing its result, which belongs to
`fp.to_ieee_bv`.

## Building and running

It is one of the extra tools:

```sh
cmake -DBUILD_EXTRA_TOOLS=ON -DCMAKE_BUILD_TYPE=Release ..
make difficulty_bench
```

```sh
./difficulty_bench                          # everything, at 8..128 bits
./difficulty_bench --widths 32 --no-fp      # just the bit-vector operations
./difficulty_bench --no-bv                  # just the floating-point operations
./difficulty_bench --arity 4                # n-ary operands
./difficulty_bench --csv > measured.csv     # for re-fitting
```

`--widths` applies to the bit-vector operations only. The floating-point
sweep always runs the four IEEE formats, and its `width` column is the total
format width, so binary32 appears as 32 whatever `--widths` says.

Sample output (the width-32 rows of a full run):

```
operation                 width          aig        score    ratio
bvadd                        32          345          345    1.00x
bvmul                        32         5767         5767    1.00x
bvudiv                       32        20136        20148    1.00x
bvmul-const                  32          375          375    1.00x
const-bvudiv                 32        15299        15552    1.02x
bvult                        32          191          191    1.00x
fp.mul                       32        17326        17054    0.98x
  (depth 1) fp.mul           32         8843         8542    0.97x
```

The trailing summary line gives the geomean of score/aig, the spread of that
ratio, and the fraction of operations predicted within a factor of two. The
estimate is deliberately an upper bound — it assumes no sharing, and the real
AIG is hash-consed — so a geomean slightly above 1 is expected and correct.
