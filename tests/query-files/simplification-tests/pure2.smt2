; RUN: %solver --pure-literals=1 --exit-after-CNF %s | %OutputCheck %s

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)

; The below should simplify down to m.
;  108:(OR 
;  50:m
;   52:(AND 
;     48:l
;     50:m))
;(declare-fun l () Bool)
;(declare-fun m () Bool)
;(assert (or m (and l m)))

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)

; Simplifies as expected.
; (assert (or (or a b) (and a b)))

(assert (or (or a b) (or c (and a d))))


;(assert (or (or a (and a d)) (or b c)))







; CHECK-NEXT: ^sat
(check-sat)
(exit)

