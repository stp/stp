; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; SMT-LIB 2 reserves symbols beginning with '@' or '.' for solver use, and STP
; does not merely respect that reservation -- it relies on it. Its own
; introduced objects are named in that space and take the name's uniqueness on
; trust: CreateFreshVariable mints '@' names, and so do the arrays and free
; bits supplying the unspecified results of the partial floating-point
; operations, whose identity *is* their name.
;
; So a declaration here is not a naming curiosity. Declaring
; @fp_unspecified_min_zero_8x24_8x24_4 and pinning it used to decide the
; solver's own "unspecified" choice for (fp.min +zero -zero) -- the answer
; flipped with the constant -- as well as hiding the user's symbol from the
; model and, at a mismatched sort, aborting on a width assertion.
;
; CHECK: reserved for solver use
(set-logic QF_ABVFP)
(declare-fun |@fp_unspecified_min_zero_8x24_8x24_4| () (_ BitVec 4))
(assert (= |@fp_unspecified_min_zero_8x24_8x24_4| #b0010))
(assert (fp.isNegative (fp.min (_ +zero 8 24) (_ -zero 8 24))))
(check-sat)
