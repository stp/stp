; --uf-phase-hints biases the first candidate so the scalars the congruence
; checker reads start out pairwise different.
;
; The refinement loop's cost is collisions: two applications whose arguments
; read the same value and whose results do not. Nothing tells the backend that
; spreading unconstrained scalars out is worth anything, so its default phase
; puts many on the same value at once and each collision costs a lemma and
; another full solve. Counting them off against an increasing value is the
; ordinary way to seed a distinctness constraint, pointed at what the checker
; reads.
;
; Here every argument is unconstrained and the results are forced apart, so
; the hint is exactly right: with it the first candidate already has distinct
; arguments and no congruence lemma is ever earned.
;
; It is advisory -- a phase moves the search order and nothing else -- so the
; verdict is the same either way, which is what the two runs check.
;
; Distinct ordering is off in both, and not because the two interact badly:
; this is precisely the shape it recognises, and left on it chains the
; arguments and removes the collisions the test is measuring, so the
; unhinted run would find nothing to install either. Turning it off is what
; leaves the hint as the only thing separating the two runs.
;
; The observable here is the hint doing its job -- zero lemmas in the HINTED
; run -- and that needs the default backend to honour suggestPhase. CaDiCaL
; does; MiniSat and Riss accept the call and ignore it, so on those builds
; the hinted run earns lemmas exactly as the plain one and the comparison
; below pins nothing.
; REQUIRES: cadical
;
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --uf-phase-hints=1 --distinct-ordering=0 --incremental=off %s 2>&1 | %OutputCheck --check-prefix=HINTED %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --uf-phase-hints=0 --distinct-ordering=0 --incremental=off %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; HINTED-NOT: installed congruence lemma
; HINTED: ^sat$
;
; PLAIN: installed congruence lemma
; PLAIN: ^sat$
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 32)) (_ BitVec 32))
(declare-const a0 (_ BitVec 32))
(declare-const a1 (_ BitVec 32))
(declare-const a2 (_ BitVec 32))
(declare-const a3 (_ BitVec 32))
(declare-const a4 (_ BitVec 32))
(declare-const a5 (_ BitVec 32))
(declare-const a6 (_ BitVec 32))
(declare-const a7 (_ BitVec 32))
(assert (distinct (f a0) (f a1) (f a2) (f a3) (f a4) (f a5) (f a6) (f a7)))
(check-sat)
