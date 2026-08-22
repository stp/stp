; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; The named formats reach the sort rules as bare identifiers when no FP
; set-logic is in force, and the diagnostic waiting for them there is not
; merely unhelpful but wrong: "unknown sort (not built in, and not a
; declared sort)" describes a typo, whereas Float64 is built in and only
; disabled. The base message is left alone -- it is right for every other
; name that lands on that rule -- and the hint corrects it for this one.
; RoundingMode takes the same path.
; CHECK-L: hint: Float64 is a floating-point name; those are recognised only after a floating-point (set-logic): QF_FP, QF_BVFP, QF_ABVFP or one of their LRA variants
(declare-const x Float64)
(check-sat)
