; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(declare-fun y () (_ BitVec 16))
; The node factory turns an overflow predicate with a constant, identical or
; complemented operand into a comparison. Each equivalence below is the rule
; against the predicate's definition; the conjunction of their negations is
; unsat.
(assert (or
  (not (= (bvuaddo x #x0100) (bvugt x #xfeff)))
  (not (= (bvuaddo x x) (bvslt x #x0000)))
  (not (= (bvuaddo (bvnot x) y) (bvult x y)))
  (not (= (bvsaddo x #x0100) (bvsgt x #x7eff)))
  (not (= (bvsaddo x #xff00) (bvslt x #x8100)))
  (not (= (bvsaddo x (bvnot x)) false))
  (not (= (bvsaddo x (bvneg x)) (= x #x8000)))
  (not (= (bvssubo x #x0100) (bvslt x #x8100)))
  (not (= (bvssubo x #xff00) (bvsgt x #x7eff)))
  (not (= (bvssubo #x0100 x) (bvslt x #x8101)))
  (not (= (bvssubo #xff00 x) (bvsgt x #x7f00)))
  (not (= (bvumulo x #x0003) (bvugt x #x5555)))
  (not (= (bvumulo x #x8000) (bvugt x #x0001)))
  (not (= (bvsmulo x #x0003) (or (bvsgt x #x2aaa) (bvslt x #xd556))))
  (not (= (bvsmulo x #xfffd) (or (bvsgt x #x2aaa) (bvslt x #xd556))))
  (not (= (bvsmulo x #xffff) (= x #x8000)))
  (not (= (bvsmulo x #x0001) false))
  (not (= (bvusubo x y) (bvult x y)))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
