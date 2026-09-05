; RUN: %solver %s | %OutputCheck %s
;
; The NaN quotient on float array indexes must hold for symbolic indexes,
; not just literals: two variables known only to be NaN may carry different
; bit patterns, yet they name the one NaN cell, so the selects agree. This
; is the congruence the solve-time index canonicalisation (FpTotalise
; rewriting the index to canonical bits) exists to provide -- the machinery
; below it compares raw index bits.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (fp.isNaN y))
(assert (distinct (select a x) (select a y)))
; CHECK: ^unsat
(check-sat)
