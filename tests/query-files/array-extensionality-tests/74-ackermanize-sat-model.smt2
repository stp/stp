; RUN: %solver --array-equality --ackermanize --check-sanity %s | %OutputCheck %s
; CHECK: ^sat
; CHECK-L: define-fun
; A satisfiable disequality on the eager path still yields a model, the
; retired records' lowerings still resolve the public equality handle,
; and the sanity check agrees with the published cells.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 8)))
(assert (not (= a b)))
(assert (= (select a #b00) (select b #b00)))
(check-sat)
(get-model)
