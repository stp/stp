; Exact packed endpoint evaluation must respect target rounding rather than a
; host nextafter/max-ULP approximation. This exercises halfway rounding,
; directed underflow, symbolic-mode outward bounds, and signed multiplication.
;
; RUN: %solver --fp-domain-simplify=1 -s %s 2>&1 | %OutputCheck --check-prefix=DOMAIN %s
; RUN: %solver %s | %OutputCheck --check-prefix=BASE %s
; DOMAIN: FpDomainSimplify: 8 boxed symbols, [1-9][0-9]* interval-true, [1-9][0-9]* interval-false
; DOMAIN: ^sat
; BASE: ^sat
;
(set-logic QF_FP)
(declare-fun oneVar () (_ FloatingPoint 8 24))
(declare-fun halfUlpVar () (_ FloatingPoint 8 24))
(declare-fun minSubVar () (_ FloatingPoint 8 24))
(declare-fun halfVar () (_ FloatingPoint 8 24))
(declare-fun neg () (_ FloatingPoint 8 24))
(declare-fun pos () (_ FloatingPoint 8 24))
(declare-fun largest () (_ FloatingPoint 8 24))
(declare-fun two () (_ FloatingPoint 8 24))
(declare-fun rm () RoundingMode)

(define-fun one () (_ FloatingPoint 8 24)
  (fp #b0 #x7f #b00000000000000000000000))
(define-fun nextOne () (_ FloatingPoint 8 24)
  (fp #b0 #x7f #b00000000000000000000001))
(define-fun halfUlp () (_ FloatingPoint 8 24)
  (fp #b0 #x67 #b00000000000000000000000))
(define-fun minSub () (_ FloatingPoint 8 24)
  (fp #b0 #x00 #b00000000000000000000001))
(define-fun half () (_ FloatingPoint 8 24)
  (fp #b0 #x7e #b00000000000000000000000))
(define-fun minusEight () (_ FloatingPoint 8 24)
  (fp #b1 #x82 #b00000000000000000000000))
(define-fun minusThree () (_ FloatingPoint 8 24)
  (fp #b1 #x80 #b10000000000000000000000))
(define-fun maxFinite () (_ FloatingPoint 8 24)
  (fp #b0 #xfe #b11111111111111111111111))
(define-fun twoValue () (_ FloatingPoint 8 24)
  (fp #b0 #x80 #b00000000000000000000000))

; Singleton boxes make the halfway and underflow endpoints exact while still
; exercising the interval evaluator rather than constant folding.
(assert (and
  (fp.leq one oneVar) (fp.leq oneVar one)
  (fp.leq halfUlp halfUlpVar) (fp.leq halfUlpVar halfUlp)
  (fp.leq minSub minSubVar) (fp.leq minSubVar minSub)
  (fp.leq half halfVar) (fp.leq halfVar half)
  (fp.leq (fp #b1 #x80 #b00000000000000000000000) neg)
  (fp.leq neg (fp #b1 #x7f #b00000000000000000000000))
  (fp.leq (fp #b0 #x80 #b10000000000000000000000) pos)
  (fp.leq pos (fp #b0 #x81 #b00000000000000000000000))
  (fp.leq maxFinite largest) (fp.leq largest maxFinite)
  (fp.leq twoValue two) (fp.leq two twoValue)))

(assert (and
  ; 1 + 2^-24 is halfway: RNE goes to one, RNA goes to nextOne.
  (fp.leq (fp.add RNE oneVar halfUlpVar) one)
  (not (fp.leq (fp.add RNA oneVar halfUlpVar) one))
  ; Any legal symbolic mode lies between RTN and RTP.
  (fp.leq (fp.add rm oneVar halfUlpVar) nextOne)
  (not (fp.gt (fp.add rm oneVar halfUlpVar) nextOne))

  ; Half of the minimum subnormal rounds down under RNE and up under RTP.
  (fp.leq (fp.mul RNE minSubVar halfVar) (_ +zero 8 24))
  (not (fp.gt (fp.mul RNE minSubVar halfVar) (_ +zero 8 24)))
  (fp.geq (fp.mul RTP minSubVar halfVar) minSub)
  (fp.leq (fp.mul rm minSubVar halfVar) minSub)
  (fp.geq (fp.mul rm minSubVar halfVar) (_ +zero 8 24))

  ; [-2,-1] * [3,4] has exact target interval [-8,-3].
  (fp.geq (fp.mul RNE neg pos) minusEight)
  (fp.leq (fp.mul RNE neg pos) minusThree)
  (not (fp.gt (fp.mul RNE neg pos) minusThree))

  ; A non-finite endpoint makes the interval unknown; it must not justify
  ; erasing this genuine overflow classification.
  (fp.isInfinite (fp.mul RNE largest two))))
(check-sat)
(exit)
