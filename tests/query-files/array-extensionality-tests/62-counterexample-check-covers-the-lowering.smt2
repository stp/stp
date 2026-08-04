; RUN: %solver -d --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; --check-sanity (-d) re-evaluates the query the user submitted against
; the finished model. That root still carries its opaque array
; equalities, so the check runs them through their recorded lowering --
; it covers the solve-boundary transformation, rather than re-asking the
; question the verdict already answered on the lowered root, which the
; formula memo would have answered from cache.
;
; The equality here is false, so the check has to evaluate a proxy the
; solver assigned false and a witness index at which the two arrays
; genuinely differ. Injecting a wrong answer into the ARRAY_EQ
; evaluation makes this query report a bogus counterexample.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 3) (_ BitVec 4)))
(declare-fun b () (Array (_ BitVec 3) (_ BitVec 4)))
(declare-fun c () (Array (_ BitVec 3) (_ BitVec 4)))
(declare-fun i () (_ BitVec 3))
(assert (distinct a b))
(assert (= c (store a i #x3)))
(assert (= (select b i) #x5))
(check-sat)
