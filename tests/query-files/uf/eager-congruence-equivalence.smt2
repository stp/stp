; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck --check-prefix=DYNAMIC %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck --check-prefix=DYNAMIC %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=auto --incremental=off %s 2>&1 | %OutputCheck --check-prefix=EAGER %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=auto --incremental=on %s 2>&1 | %OutputCheck --check-prefix=EAGER %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=on --incremental=off %s 2>&1 | %OutputCheck --check-prefix=EAGER %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=on --incremental=on %s 2>&1 | %OutputCheck --check-prefix=EAGER %s
; RUN: %solver --uninterpreted-functions --uf-ackermann-budget=0 --incremental=off %s 2>&1 | %OutputCheck --check-prefix=ANSWER %s
;
; DYNAMIC: UF: installed congruence lemma 1 for f
; DYNAMIC: ^unsat$
;
; EAGER-NOT: UF: installed congruence lemma
; EAGER: ^unsat$
;
; ANSWER: ^unsat$
;
; The two applications are congruent because their actuals are forced equal,
; so the query is unsatisfiable either way. With eager encoding off, a
; candidate has to expose the conflict and earn the lemma; an eagerly encoded
; f already carries the implication, so the checker never sees a conflict.
; Both must reach unsat, and the dynamic checker stays active in every mode:
; an eagerly encoded declaration that still produced a conflict would expose
; a bug in the encoder rather than permit a silent wrong answer.
;
; A zero budget makes 'auto' select no declaration, exercising the same
; dynamic-only route as explicitly turning eager encoding off.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const p (_ BitVec 8))
(declare-const q (_ BitVec 8))
(assert (= p q))
(assert (distinct (f p) (f q)))
(check-sat)
