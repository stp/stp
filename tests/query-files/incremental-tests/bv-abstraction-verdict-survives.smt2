; An unrefined abstraction is an over-approximation, so it can answer sat to
; a query that is not.
;
; The persistent driver bit-blasted through a blaster that was abstracting and
; then never refined, which makes every abstracted equality a free Boolean for
; the life of the solve. A relaxation has models the query does not, and this
; query -- the smallest one found that reaches it -- is one where that showed:
; unabstracted it is unsatisfiable, and the round that noticed the candidate
; was not a model of it had no owner able to say why, so the driver stopped on
; its own guard rather than on an answer:
;
;   Fatal Error: IncrementalSolver: UF refinement rejected a candidate without
;   retaining a block-scoped lemma
;
; The guard was right that the loop could not progress. What was missing is
; the party that should have progressed it: the equality inside the rounding
; mode's carrier had been replaced by a Boolean nobody was pinning.
;
; The two legs must agree, and what they have to agree on is unsat -- a leg
; that merely does not abort would pass on a lost refutation.
;
; RUN: %solver --incremental=on --uninterpreted-functions --bv-eq-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=on --uninterpreted-functions %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^unsat$
;
; PLAIN: ^unsat$
;
(set-logic QF_UFFP)
(declare-fun x0 (Bool) Bool)
(declare-const x2 RoundingMode)
(assert (fp.isZero (ite (x0 (= RNE RNE)) (_ -oo 3 5) (fp.roundToIntegral x2 (fp #b1 #b101 #b0110)))))
(check-sat)
(exit)
