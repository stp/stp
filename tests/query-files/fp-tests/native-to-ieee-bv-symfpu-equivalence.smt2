; fp.to_ieee_bv has no SMT-LIB surface syntax in STP; FpTotalise builds it
; internally, and min/max is one of the places it does -- the selector that
; decides min(+0,-0) reads both operands' canonical sign bits through it.
; This is the same min/max miter with the native packing circuit on as well,
; so the two arms disagree if collapsing NaN to the canonical pattern with
; one mux differs from SymFPU's unpack-and-re-encode. The pack count falls
; from three to one because two of the three round trips became that mux.
;
; RUN: %solver --bb.fp-native-all=false --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-minmax=true --bb.fp-native-pack=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: FloatBlast: 3 SymFPU operations, 6 unpacks, 1 packs
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 3 4))
(declare-fun b () (_ FloatingPoint 3 4))
(declare-fun unit () (_ FloatingPoint 3 4))
(declare-fun minus-zero () (_ FloatingPoint 3 4))
(declare-fun native-min () (_ FloatingPoint 3 4))
(declare-fun oracle-min () (_ FloatingPoint 3 4))
(declare-fun native-max () (_ FloatingPoint 3 4))
(declare-fun oracle-max () (_ FloatingPoint 3 4))
(define-fun one () (_ FloatingPoint 3 4) (fp #b0 #b011 #b000))

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
