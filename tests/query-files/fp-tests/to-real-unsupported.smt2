; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; fp.to_real needs a theory of reals, which STP does not have; the
; diagnostic says so by name.
; CHECK: fp.to_real is not supported
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= (fp.to_real x) (fp.to_real x)))
(check-sat)
