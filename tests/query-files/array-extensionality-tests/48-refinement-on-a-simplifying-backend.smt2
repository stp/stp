; REQUIRES: minisat
; RUN: %solver --array-equality --simplifying-minisat %s | %OutputCheck %s
; CHECK: ^unsat
; The refinement loop on a SAT backend that eliminates variables. Same
; query as 26-define-fun-array-unsat, which the default backend decides
; in milliseconds; on the simplifying Minisat it did not terminate at
; all.
;
; Lemma encoding reifies each bit-vector equality atom into a fresh SAT
; variable and caches it, so later refinement rounds reuse it -- with
; the solver's own simplification running in between. The host's read
; axioms never do that: they build their reified variables fresh for
; every clause, which is why only this path could hand a backend a
; variable it had already eliminated. CryptoMiniSat and CaDiCaL restore
; eliminated variables when a new clause mentions them and plain
; Minisat eliminates none, so all three hid it; the simplifying Minisat
; does eliminate, and the reused variable left the added clause unable
; to rule the candidate out, so refinement never made progress.
;
; 32-reset-assertions-equality and 33-get-model-content hung the same
; way. Freezing the cached variables fixes all three.
(set-logic QF_ABV)
(declare-fun base () (Array (_ BitVec 2) (_ BitVec 2)))
(define-fun A0 () (Array (_ BitVec 2) (_ BitVec 2)) (store (store base #b00 #b01) #b10 #b11))
(define-fun A1 () (Array (_ BitVec 2) (_ BitVec 2)) (store (store base #b10 #b11) #b00 #b01))
(assert (distinct A0 A1))
(check-sat)
