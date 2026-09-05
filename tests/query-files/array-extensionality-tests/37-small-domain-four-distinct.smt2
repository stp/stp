; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The exact boundary of the previous test: four pairwise distinct
; arrays saturate the (Array (_ BitVec 1) (_ BitVec 1)) domain and are
; still satisfiable -- the n-ary distinct expands to six abstracted
; disequalities whose witnesses must all be honored at once.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun c () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun d () (Array (_ BitVec 1) (_ BitVec 1)))
(assert (distinct a b c d))
(check-sat)
