; REQUIRES: cadical
; RUN: %solver --cadical --incremental-auto-engage-at=1 --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-const-width=8 %s | %OutputCheck %s
; RUN: %solver --cadical --incremental=on -d --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-const-width=8 %s | %OutputCheck %s
; RUN: %solver --cadical -d --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-const-width=8 %s | %OutputCheck %s
;
; The push/pop fuzzing's reduction of the same defect on the whole-stack
; block route: the first query's block mints the signed remainder's
; quotient-remainder pair, the second query's block re-mints it, and the
; abstracted equality over the first pair certified a candidate that the
; raw stack evaluates false. With every read axiom and congruence lemma
; already in place the driver aborted:
;   an array-equality round fell back to read refinement, rejected the
;   candidate and emitted no new logical axiom
; Which candidate the search proposes depends on the backend, and CaDiCaL
; is the one that exposes it.
(declare-const x (_ BitVec 1))
(declare-fun f ((_ BitVec 9) (_ BitVec 12)) (_ BitVec 4))
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 1)))
(assert (= (_ bv0 7) ((_ sign_extend 3) (bvsrem (f (_ bv0 9) (_ bv0 12)) (f (_ bv0 9) ((_ sign_extend 1) (bvsrem ((_ sign_extend 4) ((_ zero_extend 6) x)) (_ bv17 11))))))))
(push 1)
; CHECK: ^sat
(check-sat)
(assert (bvuge ((_ sign_extend 3) (select a ((_ zero_extend 3) (select a (_ bv0 4))))) (f ((_ sign_extend 5) (f (_ bv0 9) (_ bv0 12))) (_ bv0 12))))
; CHECK-NEXT: ^sat
(check-sat)
