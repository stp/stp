; Compare the native add and multiply circuits with independent SymFPU
; encodings over every value of (3,4) and every rounding mode. FMA by a
; symbolic value constrained to 1 expresses addition without being rewritten
; to fp.add. The inner FMA with -0 similarly keeps the multiplication oracle
; off the native packed path. Structural equality detects signed-zero
; disagreements; NaN payloads are deliberately ignored.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-arith=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: FloatBlast: 3 SymFPU operations, 6 unpacks
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 3 4))
(declare-fun b () (_ FloatingPoint 3 4))
(declare-fun unit () (_ FloatingPoint 3 4))
(declare-fun minus-zero () (_ FloatingPoint 3 4))
(declare-fun rm () RoundingMode)
(declare-fun native-add () (_ FloatingPoint 3 4))
(declare-fun oracle-add () (_ FloatingPoint 3 4))
(declare-fun native-mul () (_ FloatingPoint 3 4))
(declare-fun oracle-mul () (_ FloatingPoint 3 4))
(define-fun one () (_ FloatingPoint 3 4) (fp #b0 #b011 #b000))

(assert (fp.leq one unit))
(assert (fp.leq unit one))
(assert (fp.isZero minus-zero))
(assert (fp.isNegative minus-zero))
(assert (= native-add (fp.add rm a b)))
(assert (= oracle-add (fp.fma rm a unit b)))
(assert (= native-mul (fp.mul rm a b)))
(assert (= oracle-mul
           (fp.mul rm (fp.fma RNE a unit minus-zero) b)))
(assert
  (or
    (not (or (= native-add oracle-add)
             (and (fp.isNaN native-add) (fp.isNaN oracle-add))))
    (not (or (= native-mul oracle-mul)
             (and (fp.isNaN native-mul) (fp.isNaN oracle-mul))))))
(check-sat)
(exit)
