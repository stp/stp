# UFSTP batch/persistent equivalence

`reference-profile.smt2` is executed once through the fresh-query batch route
and once through the exact-stack persistent route. The wider `uf` directory
does the same for every semantic, lifecycle, array/FP boundary, and model
fixture, covering `DR-T-MODE-EQUIV-01` without enabling an optional eager or
batched-lemma profile.
