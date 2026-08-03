; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; The far end of the family roundtointegral-format-refused.smt2 pins the near
; end of. symfpu's off-by-one bites wherever the unpacked exponent width
; equals the significand width, which is (eb, eb+1) for every eb >= 3 -- an
; unbounded family, so the refusal has to hold at the top as well as at
; (_ FloatingPoint 4 5).
;
; It did not. FloatBlaster::unpackedExponentWidth replicates symfpu's
; exponentWidth, and its guard against overflowing the shift in the last
; branch sat above the branch before it, which does not shift. From eb = 63 up
; the guard answered for the short-significand case too -- UINT_MAX rather
; than eb + 1 -- so the widths no longer compared equal and the refusal did not
; fire. (_ FloatingPoint 63 64) got as far as the blaster and came out through
; the matchWidth backstop, complaining that formatSupported should have
; refused it, instead of being turned away here with the format named.
;
; Cheap to run despite the width: the refusal is at parse time, so no circuit
; is ever built.
; CHECK: fp.roundToIntegral is not supported at this format
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 63 64))
(assert (not (fp.eq (fp.roundToIntegral RNE x) x)))
(check-sat)
