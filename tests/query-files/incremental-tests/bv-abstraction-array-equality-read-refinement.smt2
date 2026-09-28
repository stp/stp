; An array-equality round on the driver's route reaches its read-refinement
; fallback, and the abstraction is what put it there.
;
; A store equality over an extensional array is decided by the array-equality
; machinery, which refines by emitting axioms and expects every round it drives
; to leave at least one behind. --bv-eq-abstraction replaces the equalities the
; round reads with free Booleans, so the candidate it was handed disagreed with
; the query for a reason no array owner could state, and the round fell through
; to read refinement with nothing to emit:
;
;   Fatal Error: IncrementalSolver: an array-equality round fell back to read
;   refinement, rejected the candidate and emitted no new logical axiom -- the
;   encoding and model evaluation disagree
;
; The driver owns the abstraction now and pins it before an array round sees
; the candidate, so the round is handed an assignment it can act on.
;
; The index and element sorts are RoundingMode rather than bit-vectors because
; that is the shape the fuzzer found, and it is not incidental: a rounding mode
; is carried as a five-bit vector whose legal values are constrained, so the
; equalities the round reads are exactly the ones the abstraction replaces.
;
; The second leg is the control: without the abstraction the same query is
; answered the same way, so what this pins is the encoding, not the query.
;
; RUN: %solver --incremental=on --array-equality -d --bv-eq-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=on --array-equality -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_ABVFP)
(declare-const m RoundingMode)
(declare-const a (Array RoundingMode RoundingMode))
(assert (= (store a m m) a))
(check-sat)
(exit)
