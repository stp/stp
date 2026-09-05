# Typed uninterpreted-function frontend golden tests

These tests pin feature/logic independence, top-level namespace collisions,
lexer token classification, define-fun and let priority, and atomic
rejection: a malformed command is refused as a unit and the session ends
there, so a case that needs its own run has its own input under `Inputs/`.
The production grammar is generated with `%expect 0`; any Bison conflict is a
build failure.
