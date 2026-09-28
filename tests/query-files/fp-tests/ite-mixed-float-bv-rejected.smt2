; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; Equal packed widths do not make FloatingPoint and BitVec the same sort. The
; constant condition ensures the parser checks before the factory folds the ite.
; CHECK: ite branches must have the same sort
(set-logic QF_BVFP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isZero (ite true x #x00000000)))
(check-sat)
