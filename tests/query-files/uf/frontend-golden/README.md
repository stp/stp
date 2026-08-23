# Typed uninterpreted-function frontend golden tests

These tests pin feature/logic independence, top-level namespace collisions,
lexer token classification, define-fun and let priority, atomic nonfatal
rejection, and parser recovery. The production grammar is generated with
`%expect 0`; any Bison conflict is a build failure.
