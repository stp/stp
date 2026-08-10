; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
;
; fp.roundToIntegral used to be refused wherever SymFPU's unpacked exponent
; width equalled the significand width -- an unbounded family, (eb, eb+1) for
; every eb >= 3, so (4,5) and (8,9) and upwards. roundToIntegral resizes a
; rounding point of width exponentWidth + 1 with matchWidth, which may only
; widen, on a guard that admitted equality; the value was then one bit too
; wide for it.
;
; patches/symfpu/0003 makes that guard strict, so the extract arm runs where
; the widths are equal -- which the collar above it already made safe. These
; are the smallest and a larger member of the family, plus (2,3), which is in
; it only because 0002 made the format reachable at all.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 4 5))
(declare-fun b () (_ FloatingPoint 8 9))
(declare-fun c () (_ FloatingPoint 2 3))

(assert (not (and
  ; rounding an already-integral value changes nothing, and infinities and
  ; zeros are integral
  (= (fp.roundToIntegral RNE (_ +oo 4 5)) (_ +oo 4 5))
  (= (fp.roundToIntegral RNE (_ -zero 4 5)) (_ -zero 4 5))
  (fp.isNaN (fp.roundToIntegral RNE (_ NaN 4 5)))
  ; the result is always integral, so rounding twice is rounding once
  (= (fp.roundToIntegral RNE (fp.roundToIntegral RNE a))
     (fp.roundToIntegral RNE a))
  (= (fp.roundToIntegral RTZ (fp.roundToIntegral RTZ b))
     (fp.roundToIntegral RTZ b))
  (= (fp.roundToIntegral RTP (fp.roundToIntegral RTP c))
     (fp.roundToIntegral RTP c))
  ; and it never moves a value by a whole unit in either direction
  (=> (fp.isNormal a) (fp.leq (fp.roundToIntegral RTN a) a))
  (=> (fp.isNormal a) (fp.geq (fp.roundToIntegral RTP a) a))
)))
(check-sat)
(exit)
