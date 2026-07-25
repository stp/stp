; RUN: %solver --aig-core-simplification=1 %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :status unsat)
; All four clauses over two theory atoms, so unsatisfiable propositionally
; whatever the atoms mean. Collapsing that is what the AIG rewrite of the
; propositional core is for, so this checks the rewritten core is converted
; back faithfully, not merely that the pass runs without crashing.
;
; The atoms are deliberately not asserted as top-level units: that way the
; earlier simplifications cannot dispatch the contradiction on their own, and
; the pass really does see a non-constant formula.
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (or (bvuaddo x y) (bvumulo x y)))
(assert (or (not (bvuaddo x y)) (bvumulo x y)))
(assert (or (bvuaddo x y) (not (bvumulo x y))))
(assert (or (not (bvuaddo x y)) (not (bvumulo x y))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
