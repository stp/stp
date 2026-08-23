; RUN: %solver --fp-domain-sound-zero-facts=1 -s %s 2>&1 | %OutputCheck --check-prefix=DOMAIN %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck --check-prefix=SYMFPU %s
;
; DOMAIN: 2 sound-zero-rows, 0 sound-zero-facts
; DOMAIN: ^sat
; SYMFPU: ^sat
;
; Equal/opposite terms may not be algebraically cancelled through a rounded
; FP row. Here x = y = 1 and z is the minimum subnormal. RNE loses z in
; x + z, so (x + z) - y is zero even though z is nonzero. The old inference
; cancelled x/y and unsoundly emitted magnitude(z) = 0.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))

(assert (fp.leq (_ +zero 8 24) x))
(assert (fp.leq x (fp #b0 #x80 #b00000000000000000000000)))
(assert (fp.leq (_ +zero 8 24) y))
(assert (fp.leq y (fp #b0 #x80 #b00000000000000000000000)))
(assert (fp.leq (_ +zero 8 24) z))
(assert (fp.leq z (fp #b0 #x80 #b00000000000000000000000)))

(assert (= x (fp #b0 #x7f #b00000000000000000000000)))
(assert (= y (fp #b0 #x7f #b00000000000000000000000)))
(assert (= z (fp #b0 #x00 #b00000000000000000000001)))
(assert (fp.eq (fp.add RNE x (fp.neg y)) (_ +zero 8 24)))
(assert
  (fp.eq (fp.add RNE (fp.add RNE x z) (fp.neg y)) (_ +zero 8 24)))
(assert (not (fp.isZero z)))
(check-sat)
(exit)
