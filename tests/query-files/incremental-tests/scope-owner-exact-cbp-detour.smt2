; The assertion ledger and CBP's processed-prefix cursor are deliberately
; independent.  An exact array-equality query changes the active snapshot but
; does not run ordinary CBP synchronization; the next ordinary query must
; still see that divergence and roll the old y=1 fixing back before accepting
; the replacement y=2 scope.
; RUN: %solver --array-equality --incremental --incremental-profile %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))
(assert (= x #b00))

(push 1)
(assert (= y (bvadd x #b01)))
; CHECK: ^sat
(check-sat)
(pop 1)

; This route reconciles the scope ledger but intentionally bypasses CBP.
(push 1)
(assert (= a b))
(assert (= y #b10))
; CHECK: ^sat
(check-sat)
(pop 1)

; CHECK: Incremental profile cbp/backend: check=3 cbp-resets=0 cbp-divergences=1 cbp-rollbacks=1
(push 1)
(assert (= y #b10))
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
