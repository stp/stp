; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; Nested min/max, the shape the calendar-automata families are built from,
; including an ite inside another ite's branch and inside arithmetic.
; (< a b) holds, so the value is min(b, c) = 2, and 2 + 1 = 3.
(set-logic QF_LRA)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (= a 1.0))
(assert (= b 2.0))
(assert (= c 3.0))
(assert (= (+ (ite (< a b) (ite (< b c) b c) a) 1.0) 3.0))
; CHECK: ^sat
(check-sat)
