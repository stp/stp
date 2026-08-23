; Finite semantic-sign facts let native add/mul omit sign-controlled
; cancellation and rounding circuitry. The nonnegative lower bounds
; intentionally admit -0, so the specialized paths must retain explicit
; signed-zero handling.
;
; RUN: %solver --bb.fp-native-arith=1 --fp-domain-simplify=1 --bb.fp-native-domain=1 --bb.fp-native-known-sign=1 -s %s 2>&1 | %OutputCheck --check-prefix=NATIVE %s
; RUN: %solver --bb.fp-native-arith=1 --fp-domain-simplify=1 --bb.fp-native-domain=1 --bb.fp-native-known-sign=1 -s %s 2>&1 | %OutputCheck --check-prefix=COUNTERS %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck --check-prefix=SYMFPU %s
;
; NATIVE: ^unsat
; SYMFPU: ^unsat
; COUNTERS: FP native domain known-positive add paths: [1-9][0-9]*
; COUNTERS: FP native domain known-positive mul paths: [1-9][0-9]*
;
(set-logic QF_FP)
(declare-fun pz () (_ FloatingPoint 8 24))
(declare-fun nz () (_ FloatingPoint 8 24))
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun tiny () (_ FloatingPoint 8 24))
(declare-fun half () (_ FloatingPoint 8 24))
(declare-fun largest () (_ FloatingPoint 8 24))
(declare-fun two () (_ FloatingPoint 8 24))

(define-fun maxFinite () (_ FloatingPoint 8 24)
  (fp #b0 #xfe #b11111111111111111111111))
(define-fun one () (_ FloatingPoint 8 24)
  (fp #b0 #x7f #b00000000000000000000000))
(define-fun nextOne () (_ FloatingPoint 8 24)
  (fp #b0 #x7f #b00000000000000000000001))
(define-fun halfUlpAtOne () (_ FloatingPoint 8 24)
  (fp #b0 #x67 #b00000000000000000000000))
(define-fun minSub () (_ FloatingPoint 8 24)
  (fp #b0 #x00 #b00000000000000000000001))

; All variables are finite and semantically nonnegative. In particular, these
; facts say neither that a value is nonzero nor that its sign bit is clear.
(assert (and
  (fp.leq (_ +zero 8 24) pz) (fp.leq pz maxFinite)
  (fp.leq (_ +zero 8 24) nz) (fp.leq nz maxFinite)
  (fp.leq (_ +zero 8 24) a) (fp.leq a maxFinite)
  (fp.leq (_ +zero 8 24) b) (fp.leq b maxFinite)
  (fp.leq (_ +zero 8 24) tiny) (fp.leq tiny maxFinite)
  (fp.leq (_ +zero 8 24) half) (fp.leq half maxFinite)
  (fp.leq (_ +zero 8 24) largest) (fp.leq largest maxFinite)
  (fp.leq (_ +zero 8 24) two) (fp.leq two maxFinite)))

; Pin values through FP predicates, leaving the arithmetic terms intact for
; native lowering. The two zeros retain opposite packed signs.
(assert (and
  (fp.isZero pz) (fp.isPositive pz)
  (fp.isZero nz) (fp.isNegative nz)
  (fp.eq a one)
  (fp.eq b halfUlpAtOne)
  (fp.eq tiny minSub)
  (fp.eq half (fp #b0 #x7e #b00000000000000000000000))
  (fp.eq largest maxFinite)
  (fp.eq two (fp #b0 #x80 #b00000000000000000000000))))

; Refute all target results together. This covers the signed-zero exception,
; every rounding direction at a halfway addition, exact subnormal addition,
; positive overflow, positive underflow, and nested fact propagation.
(assert
  (not
    (and
      (= (fp.add RNE pz nz) (_ +zero 8 24))
      (= (fp.add RNA pz nz) (_ +zero 8 24))
      (= (fp.add RTP pz nz) (_ +zero 8 24))
      (= (fp.add RTZ pz nz) (_ +zero 8 24))
      (= (fp.add RTN pz nz) (_ -zero 8 24))
      (= (fp.add RNE nz nz) (_ -zero 8 24))

      (= (fp.add RNE a b) one)
      (= (fp.add RNA a b) nextOne)
      (= (fp.add RTP a b) nextOne)
      (= (fp.add RTN a b) one)
      (= (fp.add RTZ a b) one)
      (= (fp.add RNE tiny tiny)
         (fp #b0 #x00 #b00000000000000000000010))
      (= (fp.add RNE largest largest) (_ +oo 8 24))
      (= (fp.add RNA largest largest) (_ +oo 8 24))
      (= (fp.add RTP largest largest) (_ +oo 8 24))
      (= (fp.add RTN largest largest) maxFinite)
      (= (fp.add RTZ largest largest) maxFinite)

      (= (fp.mul RNE nz two) (_ -zero 8 24))
      (= (fp.mul RTN nz nz) (_ +zero 8 24))
      (= (fp.mul RNE tiny half) (_ +zero 8 24))
      (= (fp.mul RTN tiny half) (_ +zero 8 24))
      (= (fp.mul RTZ tiny half) (_ +zero 8 24))
      (= (fp.mul RNA tiny half) minSub)
      (= (fp.mul RTP tiny half) minSub)
      (= (fp.mul RNE largest two) (_ +oo 8 24))
      (= (fp.mul RNA largest two) (_ +oo 8 24))
      (= (fp.mul RTP largest two) (_ +oo 8 24))
      (= (fp.mul RTN largest two) maxFinite)
      (= (fp.mul RTZ largest two) maxFinite)

      (= (fp.add RNE (fp.mul RNE a two) a)
         (fp #b0 #x80 #b10000000000000000000000)))))
(check-sat)
(exit)
