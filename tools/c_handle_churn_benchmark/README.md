# C handle-churn benchmark

This benchmark isolates the lifetime cost of repeatedly creating the same
hash-consed bit-vector constant and immediately releasing its public `Expr`
wrapper. `--uf` enables the live C handle registry; the default measures the
legacy C path. Each invocation performs one million iterations by default.

Build the `c_handle_churn_benchmark` target in a Release build, run each mode
as a fresh process three times, and compare the median `seconds` and
`peak_rss_kib` fields:

```sh
cmake --build build-release --target c_handle_churn_benchmark
for mode in legacy uf; do
  for repetition in 1 2 3; do
    if test "$mode" = uf; then
      build-release/tools/c_handle_churn_benchmark/c_handle_churn_benchmark --uf
    else
      build-release/tools/c_handle_churn_benchmark/c_handle_churn_benchmark
    fi
  done
done
```

Peak RSS is reported in KiB on Unix-like systems and as zero where the host
cannot expose it. Linux uses `/proc/self/status` so a shell tail-exec cannot
pollute the measurement with the shell's earlier high-water mark. Treat it as
a regression signal, not a portable absolute threshold: the selected
allocator and shared-library loader affect the baseline.
