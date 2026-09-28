; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; fp.abs clears the sign, so its result is never below +0: for NaN the
; ordering is false outright, for -0 the cleared sign gives +0 and the
; zeros compare equal, and everything else is non-negative. The comparison
; operand is fp.abs over a symbol, so the native path keeps the comparison
; and zeroes the packed sign bit (BBTerm's FP_ABS arm); to_fp over constant
; bits is the interned +0, resolved by the gate's constant lookthrough.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.lt (fp.abs x) ((_ to_fp 8 24) #x00000000)))
(check-sat)
(exit)
