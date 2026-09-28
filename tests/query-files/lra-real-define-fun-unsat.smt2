; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The same macro used twice in one constraint, and refuted: min(2,7) is 2,
; not 7, so this cannot hold.
(set-logic QF_LRA)
(define-fun mymin ((x Real) (y Real)) Real (ite (< x y) x y))
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= a 2.0))
(assert (= b 7.0))
(assert (= (+ (mymin a b) (mymin b a)) 14.0))
; CHECK: ^unsat
(check-sat)
