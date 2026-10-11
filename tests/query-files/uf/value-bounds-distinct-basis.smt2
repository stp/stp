; REQUIRES: cadical
; A late, asserted distinct basis may take the first value-bound ranks even
; though an earlier symbol also appears in applications. The four basis
; elements exhaust the two-bit carrier, and q must equal one of them.
;
; RUN: %solver --cadical --uf-sort-width=2 --incremental=off %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
; RUN: %solver --cadical --uf-sort-width=2 --incremental=off --uf-value-bounds=off %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
; CHECK: ^sat$

(set-logic QF_UF)
(declare-sort S 0)
(declare-fun f (S) S)
(declare-fun q () S)
(declare-fun a () S)
(declare-fun b () S)
(declare-fun c () S)
(declare-fun d () S)
(assert (distinct a b c d))
(assert (or (= q a) (= q b) (= q c) (= q d)))
(assert (= (f q) b))
(assert (= (f a) c))
(check-sat)
