; RUN: %solver --fp-domain-row-bounds=1 -s %s 2>&1 | %OutputCheck --check-prefix=DOMAIN %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck --check-prefix=SYMFPU %s
;
; DOMAIN: 1 row-bound-rows, 1 row-bound-false
; DOMAIN: ^unsat
; SYMFPU: ^unsat
;
; Target-format endpoints retain the rounding at each associated operation.
; RNE rounds x+minSub back to one, after which subtracting nextOne is exactly
; one negative ulp. The old global ULP error envelope was too loose here.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))

(define-fun one () (_ FloatingPoint 8 24)
  (fp #b0 #x7f #b00000000000000000000000))
(define-fun nextOne () (_ FloatingPoint 8 24)
  (fp #b0 #x7f #b00000000000000000000001))
(define-fun minSub () (_ FloatingPoint 8 24)
  (fp #b0 #x00 #b00000000000000000000001))

(assert (and (fp.leq one x) (fp.leq x one)))
(assert (and (fp.leq minSub z) (fp.leq z minSub)))
(assert
  (fp.eq (fp.add RNE (fp.add RNE x z) (fp.neg nextOne))
         (_ +zero 8 24)))
(check-sat)
(exit)
