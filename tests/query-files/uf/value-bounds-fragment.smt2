; REQUIRES: cadical
; AUTO selects the value bounds only for pure QF_UF. An explicit ON is also
; available for a QF_UFBV script with a declared sort.
;
; RUN: %solver --cadical -s %s 2>&1 | %OutputCheck --check-prefix=AUTO %s
; RUN: %solver --cadical -s --uf-value-bounds=on %s 2>&1 | %OutputCheck --check-prefix=ON %s
;
; AUTO-NOT: UF: bounded
; AUTO: ^sat$
; ON: UF: bounded [1-9][0-9]* declared-sort scalars by symmetry rank
; ON: ^sat$

(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun f (S) S)
(declare-fun a () S)
(assert (distinct (f a) a))
(check-sat)
