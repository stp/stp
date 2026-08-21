# UFSTP typed frontend golden tests

These tests cover `DR-T-GRAMMAR-01`, `T-FE-04`, `T-FE-05`, `T-FE-07`, and
`T-FE-08`: feature/logic independence, top-level namespace collisions,
define-fun and let priority, atomic nonfatal rejection, and parser recovery.
The production grammar is generated with `%expect 0`; any Bison conflict is a
build failure.
