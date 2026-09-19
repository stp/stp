; One product of the sum is used by another assertion, so it is built
; whatever this sum does and the pass leaves it whole; the other two are the
; sum's own and are factored. Run with -d so the model is rebuilt and checked
; against the query as written, which is what catches a factored group whose
; value changed.
; RUN: %solver -s -d --flattening=1 --common-factor=1 %s 2>&1 | %OutputCheck %s
; CHECK: Multiplications saved:1
; CHECK: ^sat$
;
; RUN: %solver -d --common-factor=0 %s | %OutputCheck --check-prefix=OFF %s
; OFF: ^sat$
(set-logic QF_BV)
(declare-fun z () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(assert (= (bvadd (bvmul z a) (bvmul z b) (bvmul z c)) (_ bv60 8)))
(assert (bvugt (bvmul z a) (_ bv200 8)))
(assert (bvugt b (_ bv1 8)))
(assert (distinct a b c))
(check-sat)
(exit)
