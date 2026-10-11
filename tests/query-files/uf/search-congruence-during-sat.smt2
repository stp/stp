; REQUIRES: cadical
; Three-bit sort carriers suffice for the ground terms in this query.
; RUN: %solver --cadical --incremental=off --uf-search-conflicts=1 --uf-ackermann=off --uf-sort-width=3 --uf-propagate-equalities=off --uf-skeleton-preproc=off -s %s 2>&1 | %OutputCheck %s
; CHECK: UF search congruence: applications=3, conflicts=[1-9][0-9]*
; CHECK: ^unsat
; CHECK: ^sat
;
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(push 1)
(assert (or (= a b) (= a c)))
(assert (distinct (f a) (f b) (f c)))
(check-sat)
(pop 1)
(assert (distinct a b))
(assert (= (f a) (f b)))
(check-sat)
