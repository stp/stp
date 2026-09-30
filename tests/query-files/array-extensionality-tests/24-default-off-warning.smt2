; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat$
; Array equality under a true disjunct is legal without a separate flag.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun x () (_ BitVec 2))
(assert (or true (= a b)))
(assert (or true (= b a)))
(assert (= x #b01))
(check-sat)
