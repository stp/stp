; RUN: %solver %s | %OutputCheck %s
; CHECK: ^unsat
;
; Lowering the floating-point layer leaves the formula pure bitvector, but a
; float symbol keeps its declared format, and an if-then-else over one goes on
; deriving a format from it: (ite c (fp.abs x) x) is an ordinary 64-bit
; if-then-else once lowered, and still answers 11/53 because its else branch is
; x. The simplifier then folds the condition -- it is a tautology, though not
; one the node factory sees as the term is built -- and carried the format
; across the rebuild onto the bitvector circuit the then branch had become:
;
;   Assertion `_ew == 0 || Degree() == 0 || is_FP_kind(GetKind())
;              || GetKind() == FLOATINGPOINT || GetIndexWidth() > 0'
;
; aborting in builds with assertions on input that needs no floating-point
; reasoning to answer. See tests/api/C/fp-lowered-ite-fold.cpp for the C API's
; half of the same bug, and for what the term means once the fold is allowed
; to drop the format.
;
; Unsatisfiable for a reason that has nothing to do with the if-then-else: no
; float is both a zero and an infinity.
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun b () (_ BitVec 1))
(assert (fp.eq x
          (fp.neg
            (fp.abs
              (ite (not (not (=> (and (bvult (bvnor b b) b)
                                      (fp.gt (_ +zero 11 53) x))
                                 (fp.gt (_ +zero 11 53) x))))
                   (fp.abs x)
                   x)))))
(assert (fp.isZero x))
(assert (fp.isNegative x))
(assert (fp.isInfinite x))
(check-sat)
