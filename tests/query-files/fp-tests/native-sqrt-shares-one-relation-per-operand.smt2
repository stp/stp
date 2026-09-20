; Two square roots of one operand under two rounding modes must name one
; (q, r), not two. Everything the native circuit builds between the unpack
; and the rounder is a function of the operand alone, so the rounding mode
; belongs in the rounder and nowhere earlier; keying the blaster's memo on
; the whole FP_SQRT node put it everywhere. Two relations leave the search
; ranging over (x, q1, r1, q2, r2) instead of (x, q, r), which is
; exponential in the significand: this query is Theorem 19 of the Handbook
; of Floating-Point Arithmetic at float32, and it took 3,497 seconds to
; refute with two relations against 0.03 with one.
;
; RUN: %solver --bb.fp-native-sqrt=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: fp-native: relational encodings minted: 1
; CHECK: fp-native: square roots sharing an earlier relation: 1
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun x () Float32)
(assert (not (= (fp.sqrt RNE x) (fp.sqrt RNA x))))
(check-sat)
(exit)
