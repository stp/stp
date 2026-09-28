; reset-assertions keeps declarations and drops assertions -- including the
; one-hot pin a RoundingMode declaration asserted for itself. The symbol is
; still a legal leaf afterwards, and UF lowering registers it as a checker
; authority the moment it appears as an actual, so lowering pins every
; RoundingMode solve scalar it registers rather than assuming an earlier
; assertion is still there.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(set-option :global-declarations true)
(declare-fun k (RoundingMode) RoundingMode)
(declare-const r RoundingMode)
; The introduced result symbol has to name a mode.
(assert (distinct (k r) RNE))
(assert (distinct (k r) RTZ))
(assert (distinct (k r) RTP))
(assert (distinct (k r) RTN))
(assert (distinct (k r) RNA))
(check-sat)
(reset-assertions)
; And so does the declared leaf actual, whose own pin has just been dropped.
(assert (= (k r) (k r)))
(assert (distinct r RNE))
(assert (distinct r RTZ))
(assert (distinct r RTP))
(assert (distinct r RTN))
(assert (distinct r RNA))
(check-sat)
(echo "REACHED-END")
