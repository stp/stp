; RoundingMode in a domain position. Carrier bit-equality is the sort's own
; equality here -- each of the five modes is exactly one 5-bit pattern -- so
; the ordinary congruence machinery applies with no further qualification.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck --check-prefix=LAZY %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck --check-prefix=LAZY %s
; CHECK: ^unsat
;
; The lazy rows pin the five-bit RoundingMode premise going through the
; direct-CNF encoder rather than through eagerly built AST equalities, in
; both the query-local and the block-guarded host.
; LAZY: UF: installed congruence lemma 1 for f
; LAZY: ^unsat
;
(set-logic QF_UFBVFP)
(declare-fun f (RoundingMode) (_ BitVec 4))
(declare-const r RoundingMode)
(declare-const s RoundingMode)
(assert (= r s))
(assert (distinct (f r) (f s)))
(check-sat)
