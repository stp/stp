; A refuted check-sat-assuming must not poison the next assumption-free
; solve of an active array equality. The assumption level is part of the
; round's exact-stack block, so its (= j i) substitutes into the record's
; anchor equations during whole-block preprocessing; the refinement lemma
; derived under those bindings collapses to NOT-proxy (the conclusion
; folds unsatisfiable and drops). Encoded unguarded, that unit survived
; the retraction as a permanent fact, and the final check answered unsat
; on the satisfiable base stack -- two identical plain check-sats around
; it disagreed. Every lemma now carries the negated block literal, so it
; retracts with the block; the final check below must still run a driver
; array-equality round over the base-only stack and answer sat.
;
; The base assertion forces i != j (equal indices would need the cell to
; be 01 and 00 at once), so the (= j i) assumption is genuinely unsat and
; the base alone is genuinely sat.
; RUN: %solver --array-equality -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --array-equality -s %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)
(declare-const i RoundingMode)
(declare-const j RoundingMode)
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
; CHECK: array-equality round, block of 1 levels
; CHECK: ^sat
(check-sat)
(exit)
