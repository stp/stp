; RUN: %solver --fp-abstraction=true -s %s 2>&1 | %OutputCheck %s
;
; x in [3, 3.2] over y in [1.5, 1.6] is at least 1.875, and the claim puts
; the quotient below 1.8: the exponent bands say only that it is in
; [1, 2), and the significand band -- the result's top bits against the
; operands' -- refutes every candidate at once, so no candidate is ever
; checked and no divider built. Without the band the same query takes
; four value lemmas and a release.
; CHECK: 0 checks, .* 0 releases
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(declare-const y (_ FloatingPoint 11 53))
(assert (fp.leq ((_ to_fp 11 53) RNE 3.0) x))
(assert (fp.leq x ((_ to_fp 11 53) RNE 3.2)))
(assert (fp.leq ((_ to_fp 11 53) RNE 1.5) y))
(assert (fp.leq y ((_ to_fp 11 53) RNE 1.6)))
(assert (fp.lt (fp.div RNE x y) ((_ to_fp 11 53) RNE 1.8)))
(check-sat)
