; The eager Ackermann path builds its congruence premises and conclusions as
; AST equalities, straight from the signature's source sorts, where the lazy
; path builds them bit-by-bit against already-blasted SAT variables. Both
; must reach the same answer over a RoundingMode signature -- and the eager
; encoding must not make the checker report a conflict it then has to refute.
;
; RUN: %solver --uf-propagate-equalities=0 -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck --check-prefix=DYNAMIC %s
; RUN: %solver --uf-propagate-equalities=0 -s --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck --check-prefix=DYNAMIC %s
; RUN: %solver --uf-propagate-equalities=0 -s --uninterpreted-functions --uf-ackermann=on --incremental=off %s 2>&1 | %OutputCheck --check-prefix=EAGER %s
; RUN: %solver --uf-propagate-equalities=0 -s --uninterpreted-functions --uf-ackermann=on --incremental=on %s 2>&1 | %OutputCheck --check-prefix=EAGER %s
; --uf-propagate-equalities=0: this test exercises the refinement loop on a
; top-level equality, which the pre-lowering pass would otherwise settle before
; any lemma is needed.
;
; DYNAMIC: UF: installed congruence lemma 1 for f
; DYNAMIC: ^unsat$
;
; EAGER-NOT: UF: installed congruence lemma
; EAGER: ^unsat$
;
(set-logic QF_UFBVFP)
(declare-fun f (RoundingMode) RoundingMode)
(declare-const r RoundingMode)
(declare-const s RoundingMode)
(assert (= r s))
(assert (distinct (f r) (f s)))
(check-sat)
