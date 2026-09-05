; QF_UF is a supported UF logic in its own right. It enables non-nullary
; declarations and declared sorts without requiring a bit-vector theory in
; the input or the nonstandard --uninterpreted-functions switch.
;
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NOT: Wrong input logic
; CHECK: ^unsat
;
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-fun f (U) U)
(assert (= a b))
(assert (distinct (f a) (f b)))
(check-sat)
