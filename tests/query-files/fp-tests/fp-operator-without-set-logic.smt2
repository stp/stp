; RUN: %solver %s 2>&1 | %OutputCheck %s
;
; The third shape the gate's failures take: an operator rather than a sort.
; Here bison has no expected-token list to offer at all, so without the hint
; the entire diagnosis is "unexpected STRING_TOK  token: fp.isNaN".
; CHECK-L: hint: fp.isNaN is a floating-point name; those are recognised only after a floating-point (set-logic): QF_FP, QF_BVFP, QF_ABVFP, QF_UFFP, QF_UFBVFP, QF_AUFBVFP or one of their LRA variants
(declare-const x (_ BitVec 8))
(assert (fp.isNaN x))
(check-sat)
