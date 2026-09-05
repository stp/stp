; With the supported/default :global-declarations false, reset-assertions
; removes base-level declarations and definitions as well as assertions.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
(reset-assertions)
; Redeclaring the same name at a different sort must now be legal.
(declare-fun x () (_ BitVec 8))
(assert (= x #x22))
; CHECK-NEXT: ^sat
(check-sat)
