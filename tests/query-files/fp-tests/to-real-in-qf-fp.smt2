; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
;
; fp.to_real is part of the FloatingPoint theory, so QF_FP has it (the Real
; sort itself cannot be declared there); a conversion equals itself.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (not (= (fp.to_real x) (fp.to_real x))))
(check-sat)
