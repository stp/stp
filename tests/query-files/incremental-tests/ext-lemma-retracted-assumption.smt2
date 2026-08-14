; A refuted check-sat-assuming must not poison later solves of an active
; array equality. The assumption level is part of the round's exact-stack
; block, so its (= j i) substitutes into the record's anchor equations
; during whole-block preprocessing; the refinement lemma derived under
; those bindings collapses to NOT-proxy (the conclusion folds
; unsatisfiable and drops). Encoded unguarded, that unit survived the
; retraction as a permanent fact over the pair-deterministic proxy
; variable, and later solves asserting the same equality answered unsat
; on satisfiable stacks. Every lemma now carries the negated block
; literal, so it retracts with the block.
;
; The base assertion forces i != j (equal indices would need the cell to
; be 01 and 00 at once), so the (= j i) assumption is genuinely unsat and
; the base alone is genuinely sat.
;
; The identical plain check after the unsat round reproduces the found
; bug on an assertions build, but a Release build answers it from the
; frontend's propagated-sat verdict cache without consulting the solver.
; The q probe makes the stack new, which no cache may answer: that final
; check must run a driver array-equality round over the grown base --
; the stats line pins that it did -- and still say sat.
; RUN: %solver --array-equality -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --array-equality -s %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)
(declare-const i RoundingMode)
(declare-const j RoundingMode)
(declare-const q Bool)
(declare-const a (Array RoundingMode (_ BitVec 2)))
(assert (= (store a i #b01) (store a j #b00)))
; CHECK: ^sat
(check-sat-assuming ((= (store a i #b01) (store a j #b00))))
; CHECK: ^sat
(check-sat)
; CHECK: ^sat
(check-sat-assuming ((= (store a i #b01) (store a j #b00))))
; CHECK: array-equality round
; CHECK: ^unsat
(check-sat-assuming ((= j i)))
; the poisoned answer was unsat, from the leaked NOT-proxy unit
; CHECK: ^sat
(check-sat)
(assert q)
; CHECK: array-equality round, block of 1 levels
; CHECK: ^sat
(check-sat)
(exit)
