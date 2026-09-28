; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
;
; SMT-LIB allows any format with eb >= 2 and sb >= 2. The narrowest of them
; used to be refused at the front door, because SymFPU's unpack aborted on
; its own INVARIANT(unpackedExWidth > exWidth): exponentWidth returned the
; format's width unchanged once sb <= 3, so the invariant read eb > eb. With
; assertions off -- what CMAKE_BUILD_TYPE=Release forces -- the widths
; underflowed and the process died, which is what the refusal was for.
;
; patches/symfpu/0002 gives those formats the headroom bit instead, so they
; are now ordinary formats. This asks for facts that are true of every
; floating-point format and false of a broken one.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 3 3))
(declare-fun y () (_ FloatingPoint 2 2))

(assert (not (and
  ; a subnormal is neither normal nor zero, and is smaller than every normal
  (=> (fp.isSubnormal x) (and (not (fp.isNormal x)) (not (fp.isZero x))))
  ; the classifications partition the values
  (or (fp.isNaN x) (fp.isInfinite x) (fp.isZero x)
      (fp.isSubnormal x) (fp.isNormal x))
  ; and are mutually exclusive on the two that are easiest to confuse here
  (not (and (fp.isSubnormal x) (fp.isNormal x)))
  ; negation is an involution that flips the sign of anything not NaN
  (= x (fp.neg (fp.neg x)))
  (=> (fp.isPositive x) (fp.isNegative (fp.neg x)))
  ; adding zero is the identity away from the zeros themselves
  (=> (fp.isNormal x) (fp.eq (fp.add RNE x (_ +zero 3 3)) x))
  ; the same at the very narrowest format SMT-LIB permits
  (= y (fp.neg (fp.neg y)))
  (or (fp.isNaN y) (fp.isInfinite y) (fp.isZero y)
      (fp.isSubnormal y) (fp.isNormal y))
)))
(check-sat)
(exit)
