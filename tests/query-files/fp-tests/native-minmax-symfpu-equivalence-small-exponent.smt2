; Compare the native fp.min and fp.max circuits with independent SymFPU
; encodings over every value of (2,5). The oracle takes the same left
; operand expressed as an FMA by a symbolic one against a symbolic minus
; zero -- the identity on every value, signed zeros included -- which keeps
; the oracle off the native packed path. Both sides read the same
; totalisation selector, so a disagreement about which zero min(+0,-0)
; returns would show up here.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-minmax=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 2 5))
(declare-fun b () (_ FloatingPoint 2 5))
(declare-fun unit () (_ FloatingPoint 2 5))
(declare-fun minus-zero () (_ FloatingPoint 2 5))
(declare-fun native-min () (_ FloatingPoint 2 5))
(declare-fun oracle-min () (_ FloatingPoint 2 5))
(declare-fun native-max () (_ FloatingPoint 2 5))
(declare-fun oracle-max () (_ FloatingPoint 2 5))
(define-fun one () (_ FloatingPoint 2 5) (fp #b0 #b01 #b0000))

(assert (fp.leq one unit))
(assert (fp.leq unit one))
(assert (fp.isZero minus-zero))
(assert (fp.isNegative minus-zero))
(assert (= native-min (fp.min a b)))
(assert (= oracle-min (fp.min (fp.fma RNE a unit minus-zero) b)))
(assert (= native-max (fp.max a b)))
(assert (= oracle-max (fp.max (fp.fma RNE a unit minus-zero) b)))
(assert (or (not (= native-min oracle-min))
            (not (= native-max oracle-max))))
(check-sat)
(exit)
