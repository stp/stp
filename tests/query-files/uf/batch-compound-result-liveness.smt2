; A UF result equated to a compound term must retain one concrete candidate
; authority.  The batch liveness registrar must not turn the compound side's
; model definition into a second, missing direct assignment for the generated
; result scalar.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(assert (= (bvadd a b) (f a)))
(check-sat)
(exit)
