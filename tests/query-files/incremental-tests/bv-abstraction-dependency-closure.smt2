; A live abstraction owns every abstraction hidden behind its free result.
;
; The first level makes the inner multiplication record live and then pops
; it. The second level reuses that multiplication underneath an abstracted
; addition. Its AIG root reaches only the addition result CI; the addition's
; record is therefore the direct owner seed and the multiplication is found
; only by taking the parent-to-child dependency closure.
;
; The old direct-CI scope retired the multiplication after the pop and did not
; reactivate it through the parent. The solver could then choose an arbitrary
; inner result, satisfy the addition, and answer sat to an unsatisfiable stack.
; -d independently evaluates the raw stack under the published model.
;
; RUN: %solver --incremental=on -d --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=on -d %s 2>&1 | %OutputCheck --check-prefix=EXACT %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
; ABSTRACTED-NEXT: ^unsat$
;
; EXACT: ^sat$
; EXACT-NEXT: ^unsat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 64))
(declare-fun y () (_ BitVec 64))
(declare-fun z () (_ BitVec 64))
(declare-fun px () Bool)
(declare-fun py () Bool)
(declare-fun pz () Bool)
(assert (=> px (= x (_ bv0 64))))
(assert (=> py (= y (_ bv0 64))))
(assert (=> pz (= z (_ bv1 64))))
(push 1)
(assert (= (bvmul x y) (_ bv0 64)))
(check-sat-assuming (px py))
(pop 1)
(push 1)
(assert (= (bvadd (bvmul x y) z) (_ bv2 64)))
(check-sat-assuming (px py pz))
(pop 1)
(exit)
