; RUN: %solver --fp-domain-row-bounds=1 -s %s 2>&1 | %OutputCheck --check-prefix=DOMAIN %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck --check-prefix=SYMFPU %s
;
; DOMAIN: 1 row-bound-rows, 0 row-bound-false
; DOMAIN: ^sat
; SYMFPU: ^sat
;
; Endpoint evaluation must preserve the source association. Although the real
; expression algebraically cancels x and leaves the nonzero z, RNE first loses
; the minimum subnormal in x+z; the following addition therefore cancels to
; +0. Flattening the row into real coefficients would miss that behavior.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))

(define-fun one () (_ FloatingPoint 8 24)
  (fp #b0 #x7f #b00000000000000000000000))
(define-fun minSub () (_ FloatingPoint 8 24)
  (fp #b0 #x00 #b00000000000000000000001))

(assert (and (fp.leq one x) (fp.leq x one)))
(assert (and (fp.leq minSub z) (fp.leq z minSub)))
(assert
  (fp.eq (fp.add RNE (fp.add RNE x z) (fp.neg x))
         (_ +zero 8 24)))
(check-sat)
(exit)
