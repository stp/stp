; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; fp.eq over the whole matrix of special values, pairwise. The operands are
; symbolic and pinned by classification, so each is free to be any witness of
; its class -- in particular the two NaNs may take different payloads and
; different signs -- and the whole matrix has to hold for every choice.
;
; fp.eq is IEEE numeric equality:
;   * the two zeros are numerically equal, so every zero pair is true;
;   * NaN is equal to nothing, itself included;
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
  ; zero vs zero: all three pairs true, signs irrelevant to fp.eq
  (fp.eq pz pz) (fp.eq pz mz) (fp.eq mz mz)
  ; NaN vs NaN: false even for the same variable, and across payloads
  (not (fp.eq n1 n1)) (not (fp.eq n1 n2)) (not (fp.eq n2 n2))
  ; infinity vs infinity: by sign
  (fp.eq pi pi) (fp.eq mi mi) (not (fp.eq pi mi))
  ; cross-class
  (not (fp.eq n1 pz)) (not (fp.eq n1 pi)) (not (fp.eq n1 one))
  (not (fp.eq pi pz)) (not (fp.eq pi one)) (not (fp.eq mi one))
  (not (fp.eq pz one)) (not (fp.eq mz one))
  ; symmetric in both operand orders
  (fp.eq mz pz) (not (fp.eq mi pi)) (not (fp.eq one pi))
)))
(check-sat)
(exit)
