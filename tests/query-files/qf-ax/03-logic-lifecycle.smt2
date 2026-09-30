; reset-assertions retains the logic; reset lets another array logic select
; its own support. Both QF_AX and QF_ABV include extensional equality.
; RUN: %solver --incremental=off %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK: ^sat$
; CHECK: ^sat$
; CHECK: REACHED-END
(set-logic QF_AX)
(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I E))
(declare-fun b () (Array I E))
(assert (= a b))
(check-sat)

(reset-assertions)
(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I E))
(declare-fun b () (Array I E))
(assert (= a b))
(check-sat)

(reset)
(set-logic QF_ABV)
(declare-fun x () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun y () (Array (_ BitVec 1) (_ BitVec 1)))
(assert (= x y))
(check-sat)
(echo "REACHED-END")
