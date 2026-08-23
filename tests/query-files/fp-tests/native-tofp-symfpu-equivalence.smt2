; Compare the native (3,5)-to-(4,3) conversion with SymFPU for every source
; value and rounding mode. The exact FMA wrapper preserves the source value
; while preventing the oracle conversion from entering the native packed
; path. Structural equality detects signed-zero disagreements; NaN payloads
; are deliberately ignored.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-arith=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: FloatBlast: 2 SymFPU operations, 4 unpacks
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 3 5))
(declare-fun unit () (_ FloatingPoint 3 5))
(declare-fun minus-zero () (_ FloatingPoint 3 5))
(declare-fun rm () RoundingMode)
(declare-fun native () (_ FloatingPoint 4 3))
(declare-fun oracle () (_ FloatingPoint 4 3))
(define-fun one () (_ FloatingPoint 3 5) (fp #b0 #b011 #b0000))

(assert (fp.leq one unit))
(assert (fp.leq unit one))
(assert (fp.isZero minus-zero))
(assert (fp.isNegative minus-zero))
(assert (= native ((_ to_fp 4 3) rm x)))
(assert (= oracle
           ((_ to_fp 4 3) rm (fp.fma RNE x unit minus-zero))))
(assert
  (not (or (= native oracle)
           (and (fp.isNaN native) (fp.isNaN oracle)))))
(check-sat)
(exit)
