; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck --check-prefix=BATCH %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck --check-prefix=BATCH %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --uf-lemmas-per-round=1 --incremental=off %s 2>&1 | %OutputCheck --check-prefix=SINGLE %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --uf-lemmas-per-round=1 --incremental=on %s 2>&1 | %OutputCheck --check-prefix=SINGLE %s
;
; BATCH: UF: installed congruence lemma 1 for f
; BATCH: UF: installed congruence lemma 2 for f
; BATCH: UF: candidate refuted by 2 congruence lemmas
; BATCH: ^unsat$
;
; SINGLE: UF: installed congruence lemma 1 for f
; SINGLE-NOT: candidate refuted by
; SINGLE: ^unsat$
;
; T-OPT-01. The three actuals are forced equal, so every candidate puts all
; three applications in one bucket, and the disequality forces three distinct
; results: two records disagree with the bucket's representative in the very
; first candidate, whatever the backend assigns. Both are refuted by that one
; unchanged assignment, so both clauses are validated and installed before the
; solver is asked again.
;
; --uf-lemmas-per-round=1 keeps the one-lemma-per-round reference profile,
; which reaches the same verdict; the batched and single paths must never
; disagree, only differ in how many rounds they take.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-const a0 (_ BitVec 4))
(declare-const a1 (_ BitVec 4))
(declare-const a2 (_ BitVec 4))
(assert (= a0 a1))
(assert (= a1 a2))
(assert (distinct (f a0) (f a1) (f a2)))
(check-sat)
