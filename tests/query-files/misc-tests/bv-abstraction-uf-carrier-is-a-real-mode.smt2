; The UF checker is never handed a candidate an abstraction has not been
; refined against.
;
; A RoundingMode is carried as a bit vector of which only five values name a
; mode. The UF congruence checker reads the carrier of an application's
; argument and result back out of the candidate model and asserts it is one of
; those five, because every carrier it can legitimately be shown was written by
; the lowering's own equations.
;
; --bv-eq-abstraction replaces those equations' equalities by free Booleans
; until refinement pins them, so the solver was free to leave the carrier on
; one of the bit patterns that denotes nothing, and the checker read it:
;
;   Fatal Error: UFCHK internal error: UFCHK read a RoundingMode carrier that
;   denotes no mode
;
; The invariant is the checker's to keep and it is not wrong; what was wrong
; is who it was asked about. The abstraction is now the first refinement owner
; consulted on a candidate, before either theory checker and before model
; evaluation, so a candidate that contradicts one never reaches them.
;
; One application of one RoundingMode function is enough to reach it.
;
; RUN: %solver --incremental=off -d --uninterpreted-functions --bv-eq-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d --uninterpreted-functions %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_UFFP)
(declare-fun f (RoundingMode) RoundingMode)
(assert (= (f RTN) RTN))
(check-sat)
