; The bit-vector-indexed twin of ext-lemma-retracted-assumption.smt2:
; the lemma-guard channel has nothing to do with the rounding-mode index
; sort, which reached it in the wild only because floating point engages
; the incremental driver from the third check while pure QF_ABV waits
; until the thirty-second. Engaged from the first check, the same
; refuted (= j i) assumption fed the same anchor substitution and left
; the same permanent unit behind before lemmas were guarded by their
; block literal.
;
; As in the twin, the plain check after the unsat round can be answered
; from the frontend's propagated-sat verdict cache on a Release build,
; so the q probe forces a genuinely new stack through a driver
; array-equality round, where the leaked unit turned the answer unsat.
; RUN: %solver --incremental-auto-engage-at 1 --array-equality -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --array-equality -s %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(declare-const i (_ BitVec 3))
(declare-const j (_ BitVec 3))
(declare-const q Bool)
(declare-const a (Array (_ BitVec 3) (_ BitVec 2)))
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
; CHECK: ^sat
(check-sat)
(assert q)
; CHECK: array-equality round, block of 1 levels
; CHECK: ^sat
(check-sat)
(exit)
