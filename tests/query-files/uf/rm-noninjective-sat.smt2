; The other corner of rm-congruence-unsat: distinct rounding modes put no
; obligation on f at all, so an interpretation that separates them exists.
; A pin that over-constrained the domain, or a congruence conclusion emitted
; where none was earned, would be caught here rather than by a wrong unsat.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
;
(set-logic QF_UFBVFP)
(declare-fun f (RoundingMode) (_ BitVec 4))
(declare-const r RoundingMode)
(declare-const s RoundingMode)
(assert (distinct r s))
(assert (distinct (f r) (f s)))
(check-sat)
