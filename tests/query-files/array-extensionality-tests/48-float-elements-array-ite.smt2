; REQUIRES: floating-point
; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A float-element array if-then-else is eliminated to a fresh
; replacement array that keeps the element format; whichever branch
; the condition selects contradicts one of the disequalities.
(set-logic QF_ABVFP)
(declare-fun p () Bool)
(declare-fun a () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(declare-fun b () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(declare-fun d () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(assert (= (ite p a b) d))
(assert (not (= a d)))
(assert (not (= b d)))
(check-sat)
