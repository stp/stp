# Uninterpreted-function batch/persistent equivalence

`core-congruence.smt2` is executed once through the fresh-query batch route
and once through the exact-stack persistent route. The wider `uf` directory
does the same for every semantic, lifecycle, array/FP boundary, and model
fixture. Together they require both solve routes to produce the same verdicts
and certified models.
