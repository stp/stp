; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
;
; Constant folding at the formats that used to be refused. The literal fold
; backend gated every operation on FloatBlaster::formatSupported, which turned
; away sb <= 3 so that its refusals matched the circuit path's; once
; patches/symfpu/0002 gave those formats their headroom bit the circuit path
; stopped refusing anything, and the gate was left refusing formats that work.
;
; Every fact below is an operation on constants, so the first run folds it in
; the simplifier and the second builds the circuit instead. The two arms have
; to agree, and both have to agree with IEEE-754.
;
; In (_ FloatingPoint 3 3) the bias is 3 and the largest finite is 14.0; in
; (_ FloatingPoint 2 2), the narrowest format SMT-LIB admits, the bias is 1,
; the largest finite is 3.0 and the only subnormal is 0.5.
;
; CHECK: ^unsat
(set-logic QF_FP)

(assert (not (and
  ; 1.0 + 1.0 = 2.0
  (= (fp.add RNE (fp #b0 #b011 #b00) (fp #b0 #b011 #b00)) (fp #b0 #b100 #b00))
  ; 8.0 + 8.0 = 16.0, past the midpoint 15.0 between 14.0 and 16.0: +oo
  (= (fp.add RNE (fp #b0 #b110 #b00) (fp #b0 #b110 #b00)) (fp #b0 #b111 #b00))
  ; the subnormal is exact here: 1.0 + 0.5 = 1.5
  (= (fp.add RNE (fp #b0 #b01 #b0) (fp #b0 #b00 #b1)) (fp #b0 #b01 #b1))
  ; 2.0 + 2.0 = 4.0, past the midpoint 3.5 between 3.0 and 4.0: +oo
  (= (fp.add RNE (fp #b0 #b10 #b0) (fp #b0 #b10 #b0)) (fp #b0 #b11 #b0))
  ; 0.5 * 0.5 = 0.25, exactly halfway to the only subnormal: ties to even
  (= (fp.mul RNE (fp #b0 #b00 #b1) (fp #b0 #b00 #b1)) (fp #b0 #b00 #b0))
  ; (_ FloatingPoint 2 4): bias 1, largest finite 3.75, smallest subnormal
  ; 0.125. Not a short significand, so the gate never meant to cover it, but
  ; its unpacked exponent comes out narrower than its significand, which is
  ; what unpackedFloat::valid used to build its bound at.
  (= (fp.add RNE (fp #b0 #b01 #b000) (fp #b0 #b01 #b000)) (fp #b0 #b10 #b000))
  (= (fp.add RNE (fp #b0 #b01 #b000) (fp #b0 #b00 #b001)) (fp #b0 #b01 #b001))
  ; and the conversions into these formats, which carried the gate separately
  (= ((_ to_fp 3 3) RNE ((_ to_fp 5 11) RNE (fp #b0 #b011 #b00)))
     (fp #b0 #b011 #b00))
  (= ((_ to_fp 3 3) RNE (_ bv2 8)) (fp #b0 #b100 #b00))
  (= ((_ to_fp_unsigned 2 2) RNE (_ bv3 8)) (fp #b0 #b10 #b1))
)))
(check-sat)
(exit)
