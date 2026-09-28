; RUN: %solver --aig-core-simplification=1 %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :status sat)
; --aig-core-simplification rewrites the propositional skeleton with AIGs,
; replacing each theory atom by a fresh boolean. Every atom below is boolean
; valued over bitvector terms, so none of them may be recursed into. The
; comparison and overflow predicates used to be absent from the list of atom
; kinds, which sent the recursion down into the bitvector terms underneath.
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (or (bvult x y) (bvule y x)))
(assert (or (bvslt x y) (bvsle y x)))
(assert (or (bvugt x y) (bvuge y x)))
(assert (or (bvsgt x y) (bvsge y x)))
(assert (or (not (bvuaddo x y)) (bvsaddo x y) p))
(assert (or (not (bvumulo x y)) (bvsmulo x y) q))
(assert (or (not (bvusubo x y)) (bvssubo x y) (not p)))
(assert (or (not (bvnego x)) (bvsdivo x y) q))
(assert (= ((_ extract 0 0) x) #b1))
(assert (and (or p q) (or (not p) q)))
; CHECK-NEXT: ^sat
(check-sat)
(exit)
