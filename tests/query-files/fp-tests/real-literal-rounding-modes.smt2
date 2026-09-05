; RUN: %solver %s | %OutputCheck %s
;
; 0.1 has an infinite binary expansion, so every format rounds it and the
; five modes pull in different directions. Expected bits agreed by
; bitwuzla (MPFR), cvc5 (SymFPU) and z3: Float16 rounds up only under RTP;
; Float32 rounds up under the nearest modes and RTP; Float64 is the classic
; 0x3FB999999999999A with 0x...99 under the downward modes.
(set-logic QF_FP)
(declare-fun h1 () (_ FloatingPoint 5 11))
(declare-fun h2 () (_ FloatingPoint 5 11))
(declare-fun h3 () (_ FloatingPoint 5 11))
(declare-fun h4 () (_ FloatingPoint 5 11))
(declare-fun h5 () (_ FloatingPoint 5 11))
(declare-fun s1 () (_ FloatingPoint 8 24))
(declare-fun s2 () (_ FloatingPoint 8 24))
(declare-fun d1 () (_ FloatingPoint 11 53))
(declare-fun d2 () (_ FloatingPoint 11 53))
(assert (= h1 ((_ to_fp 5 11) RNE 0.1)))
(assert (= h2 ((_ to_fp 5 11) RNA 0.1)))
(assert (= h3 ((_ to_fp 5 11) RTP 0.1)))
(assert (= h4 ((_ to_fp 5 11) RTN 0.1)))
(assert (= h5 ((_ to_fp 5 11) RTZ 0.1)))
(assert (= s1 ((_ to_fp 8 24) RNE 0.1)))
(assert (= s2 ((_ to_fp 8 24) RTN 0.1)))
(assert (= d1 ((_ to_fp 11 53) roundNearestTiesToEven 0.1)))
(assert (= d2 ((_ to_fp 11 53) roundTowardNegative 0.1)))
(assert (or
  (distinct h1 (fp #b0 #b01011 #b1001100110))
  (distinct h2 (fp #b0 #b01011 #b1001100110))
  (distinct h3 (fp #b0 #b01011 #b1001100111))
  (distinct h4 (fp #b0 #b01011 #b1001100110))
  (distinct h5 (fp #b0 #b01011 #b1001100110))
  (distinct s1 ((_ to_fp 8 24) #x3dcccccd))
  (distinct s2 ((_ to_fp 8 24) #x3dcccccc))
  (distinct d1 ((_ to_fp 11 53) #x3fb999999999999a))
  (distinct d2 ((_ to_fp 11 53) #x3fb9999999999999))))
; CHECK: ^unsat
(check-sat)
