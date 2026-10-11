; REQUIRES: cadical
; QF_UF value bounds preserve a model needing three distinct sort elements,
; and an incremental contradiction must disappear again after pop.
;
; RUN: %solver --cadical --incremental=off --uf-sort-width=3 -s %s 2>&1 | %OutputCheck --check-prefix=BOUNDED %s
; RUN: %solver --cadical --incremental=on  --uf-sort-width=3 -s %s 2>&1 | %OutputCheck --check-prefix=BOUNDED %s
; RUN: %solver --cadical --incremental=on  --uf-sort-width=3 -s --uf-value-bounds=off %s 2>&1 | %OutputCheck --check-prefix=OFF %s
;
; BOUNDED: UF: bounded [1-9][0-9]* declared-sort scalars by symmetry rank
; BOUNDED: ^sat$
; BOUNDED: ^unsat$
; BOUNDED: ^sat$
;
; OFF-NOT: UF: bounded
; OFF: ^sat$
; OFF: ^unsat$
; OFF: ^sat$

(set-logic QF_UF)
(declare-sort S 0)
(declare-fun f (S) S)
(declare-fun a () S)
(declare-fun b () S)
(declare-fun c () S)
(assert (distinct a b c))
(assert (= (f a) b))
(assert (= (f b) c))
(check-sat)
(push 1)
(assert (= a b))
(check-sat)
(pop 1)
(check-sat)
