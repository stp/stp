; Preserve the useful observability assertion from uf's lemma-stat cases
; without depending on that branch's adapter-specific log wording.  In both
; modes the coordinator must report that UFCHK, rather than EXTCHK or ordinary
; replay, owns the conflict which closes this query.
;
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck --check-prefix=OBS %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck --check-prefix=OBS %s
; OBS: Theory coordination: EXTCHK skipped; UFCHK conflict; ordinary replay skipped
; OBS: ^unsat
;
(set-logic QF_UFBV)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
(exit)
