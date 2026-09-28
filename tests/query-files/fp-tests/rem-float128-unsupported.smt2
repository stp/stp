; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; fp.rem past roughly binary64-sized formats is refused with a diagnostic:
; symfpu's remainder unrolls one divide step per representable exponent
; difference (2^eb + sb - 4; 32877 for Float128), so the circuit's depth is
; exponential in the exponent width. This input -- found by murxla -- used
; to build that circuit and die with a stack-overflow SIGSEGV in the
; simplifier's recursive traversal (Float16/32/64 fit; Float128 does not).
; The RoundingMode variable and fp.roundToIntegral come from the original
; fuzzer input; plain fp.rem at this format is refused the same way.
; (One directive: both phrases are on the one error line, and OutputCheck
; matches each directive on a line after the previous directive's.)
; CHECK: fp.rem is not supported at this format.*use a format no larger than binary64
(set-logic QF_FP)
(declare-const r RoundingMode)
(declare-const x (_ FloatingPoint 15 113))
(assert (fp.isNaN (fp.rem (fp.roundToIntegral r x) x)))
(check-sat)
