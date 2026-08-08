; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; SMT-LIB `=` over the whole matrix of special values, pairwise, as the
; companion to fp-eq-specials-matrix.smt2 -- the two operators disagree on
; exactly the zero and NaN rows, and running the same matrix through both is
; what pins that difference down.
;
; `=` is equality on the abstract FloatingPoint domain:
;   * +0 and -0 are DISTINCT values, so the mixed zero pair is false;
;   * there is ONE NaN, so any two NaNs are equal whatever payloads and signs
;     the solver picks for them (the both-NaN disjunct of the native BBeqFP
;     encoding -- comparing packed bits alone fails this);
;   * infinities are equal exactly when their signs agree.
; The required truth values are conjoined and negated, so any one of them
; going the wrong way makes this satisfiable.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun pz () (_ FloatingPoint 8 24))
(declare-fun mz () (_ FloatingPoint 8 24))
(declare-fun pi () (_ FloatingPoint 8 24))
(declare-fun mi () (_ FloatingPoint 8 24))
(declare-fun n1 () (_ FloatingPoint 8 24))
(declare-fun n2 () (_ FloatingPoint 8 24))
(declare-fun one () (_ FloatingPoint 8 24))

(assert (and (fp.isZero pz) (fp.isPositive pz)))
(assert (and (fp.isZero mz) (fp.isNegative mz)))
(assert (and (fp.isInfinite pi) (fp.isPositive pi)))
(assert (and (fp.isInfinite mi) (fp.isNegative mi)))
(assert (fp.isNaN n1))
(assert (fp.isNaN n2))
(assert (= one ((_ to_fp 8 24) #x3F800000)))

(assert (not (and
  ; zero vs zero: the signed zeros are two different values
  (= pz pz) (= mz mz) (not (= pz mz))
  ; NaN vs NaN: one NaN value, so true across payloads and signs
  (= n1 n1) (= n2 n2) (= n1 n2)
  ; infinity vs infinity: by sign
  (= pi pi) (= mi mi) (not (= pi mi))
  ; cross-class
  (not (= n1 pz)) (not (= n1 pi)) (not (= n1 one))
  (not (= pi pz)) (not (= pi one)) (not (= mi one))
  (not (= pz one)) (not (= mz one))
  ; symmetric in both operand orders
  (not (= mz pz)) (= n2 n1) (not (= mi pi))
)))
(check-sat)
(exit)
