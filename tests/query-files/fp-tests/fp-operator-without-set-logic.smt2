; RUN: %solver %s 2>&1 | %OutputCheck %s
;
; The third shape the gate's failures take: an operator rather than a sort.
; Here bison has no expected-token list to offer at all, so without the hint
; the entire diagnosis is "unexpected STRING_TOK  token: fp.isNaN".
; CHECK-L: hint: fp.isNaN is a floating-point name; those are recognised only after (set-logic QF_FP), (set-logic QF_BVFP) or (set-logic QF_ABVFP)
(declare-const x (_ BitVec 8))
(assert (fp.isNaN x))
(check-sat)
