; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; A product of two concrete operands is itself concrete, and is folded.
; Requiring exactly one concrete operand refused this, which a let binding
; reaches easily. 2 * 3 = 6, so x = 2.
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (let ((?c 2.0) (?d 3.0)) (= (* (* ?c ?d) x) 12.0)))
(assert (= x 2.0))
; CHECK: ^sat
(check-sat)
