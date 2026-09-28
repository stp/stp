; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
;
; A symbolic rounding mode: |y| > 1 gives |x*y| >= |x| in every mode, and
; the rule that says so is emitted with the mode as a proxy symbol.
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const rm RoundingMode)
(assert (fp.isNormal x))
(assert (fp.isNormal y))
(assert (fp.lt ((_ to_fp 8 24) #x3f800000) y))
(assert (not (fp.geq (fp.abs (fp.mul rm x y)) (fp.abs x))))
(check-sat)
