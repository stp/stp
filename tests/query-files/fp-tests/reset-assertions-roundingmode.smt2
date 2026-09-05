; RUN: %solver %s | %OutputCheck %s
;
; reset-assertions drops a base RoundingMode declaration. Redeclaring the name
; must be legal, and the replacement still denotes exactly one of five modes.
(set-logic QF_BVFP)
(declare-const r RoundingMode)
(assert (= r RNE))
; CHECK-NEXT: ^sat
(check-sat)

(reset-assertions)
(declare-const r RoundingMode)
(assert (and (distinct r RNE)
             (distinct r RNA)
             (distinct r RTP)
             (distinct r RTN)
             (distinct r RTZ)))
; CHECK-NEXT: ^unsat
(check-sat)
