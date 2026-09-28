; RUN: %solver %s | %OutputCheck %s
;
; Both sides of the array at once: '=' on the float indexes and '=' on the
; float elements. Indexes equal under '=' -- which admits two NaNs with
; different payloads -- select equal elements, and element equality is
; itself the floats' '=', not raw bits. Losing either half answers sat.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ FloatingPoint 5 11) (_ FloatingPoint 5 11)))
(declare-fun x () (_ FloatingPoint 5 11))
(declare-fun y () (_ FloatingPoint 5 11))
(assert (= x y))
(assert (not (= (select a x) (select a y))))
; CHECK: ^unsat
(check-sat)
