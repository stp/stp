; A native operation leaves a rounded record behind and the classification
; predicates read it instead of the packed bits. That is only sound if the
; record agrees with its own packing, and the flags have to be masked to the
; same priority the packing applies, not just the fields under them.
;
; fp.add raises both: subtracting infinities makes the result NaN while an
; operand is still infinite, so it sets isInf and isNaN together and lets
; packing resolve them. v - v is +0 for every finite v and NaN for an
; infinite or NaN one, so it is never infinite -- but a consumer reading
; isInf off the record directly saw it set whenever v was infinite, and
; every format and rounding mode answered sat.
;
; RUN: %solver %s 2>&1 | %OutputCheck %s
; RUN: %solver -d %s 2>&1 | %OutputCheck %s
;
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun v () (_ FloatingPoint 4 8))
(assert (fp.isInfinite (fp.sub RNA v v)))
(check-sat)
(exit)
