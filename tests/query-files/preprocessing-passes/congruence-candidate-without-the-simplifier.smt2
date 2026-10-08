; The pass simplifies each candidate before blasting it, which is a speed
; measure and nothing more. --disable-opt-inc turns the simplifier off, and
; SimplifyFormula_TopLevel asserts that it is on, so the pass used to abort on
; the first candidate it proposed instead of deciding it.
;
; The same formula as congruence-candidate-collapses-two-divisions, so the
; counts are comparable -- two proposed, one proved, unsat -- with the
; simplifier off. Proving the same candidate is the point: what gets blasted
; is the raw inequality, and it decides the same thing.
;
; --disable-simplifications is the other way to turn it off, and it reaches
; the same assertion.
; RUN: %solver -s --disable-opt-inc --congruence-candidates=1 %s 2>&1 | %OutputCheck %s
; CHECK: proposed:2 tested:2 proved:1
; CHECK: After Congruence Candidates
; CHECK: ^unsat$
;
; RUN: %solver -s --disable-simplifications --congruence-candidates=1 %s 2>&1 | %OutputCheck --check-prefix=NOSIMP %s
; NOSIMP: proved:1
; NOSIMP: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun d () (_ BitVec 16))
(assert
  (not (=
    (bvudiv (bvadd (bvmul (_ bv3 16) a) (bvsub b a)) d)
    (bvudiv (bvadd (bvadd a a) (bvadd b (_ bv0 16))) d))))
(check-sat)
(exit)
