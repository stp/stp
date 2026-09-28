; RUN: %solver --bb.fp-native-arith=1 --fp-domain-sound-zero-facts=1 --bb.fp-native-domain=1 -s %s 2>&1 | %OutputCheck --check-prefix=NATIVE %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck --check-prefix=SYMFPU %s
;
; NATIVE: 0 sound-zero-rows, 0 sound-zero-facts
; NATIVE: ^sat
; SYMFPU: ^sat
;
; A zero rounded product does not imply a zero input. Half of the minimum
; subnormal is the RNE tie between zero and that subnormal, and ties-to-even
; selects zero while x itself remains nonzero.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x (fp #b0 #x00 #b00000000000000000000001)))
(assert
  (fp.isZero
    (fp.mul RNE x (fp #b0 #x7e #b00000000000000000000000))))
(assert (not (fp.isZero x)))
(check-sat)
(exit)
