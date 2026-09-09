; The congruence checker is asked about a candidate the bit-vector
; abstraction is about to refute, not only about a faithful one: equal
; arguments implying equal results is a theorem whatever values it is
; instantiated on, so the lemma is sound either way, and asked early it goes
; in beside the abstraction's clauses instead of after the abstraction has
; spent its rounds on candidates it would have refuted outright.
;
; Both products are abstracted, so the first candidate gives them free
; values; the disequality keeps the first from being the zero its operands'
; default phases make it, so the candidate is unfaithful, and the results it
; pins them to differ while the arguments a and b are equal -- a congruence
; conflict on the same candidate. The equalities are written as pairs of
; bounds so that no substitution merges the two applications, or the two
; products, before the solve.
;
; RUN: %solver -s --uninterpreted-functions --incremental=off --uf-ackermann=off --uf-propagate-equalities=0 --uf-skeleton-preproc=0 --uf-bv-term-abstraction=on %s 2>&1 | %OutputCheck %s
; CHECK: Theory coordination: BV abstraction refined; UFCHK conflict on the same candidate
; CHECK: ^sat$
;
; Switched off, the checker waits for a faithful candidate as it used to.
; RUN: %solver -s --uninterpreted-functions --incremental=off --uf-ackermann=off --uf-propagate-equalities=0 --uf-skeleton-preproc=0 --uf-bv-term-abstraction=on --uf-check-during-bv-refinement=0 %s 2>&1 | %OutputCheck --check-prefix=LATE %s
; LATE-NOT: UFCHK conflict on the same candidate
; LATE: ^sat$
;
; EXPECT: sat, sat
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 64))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))
(declare-const z (_ BitVec 64))
(assert (bvule a b))
(assert (bvule b a))
(assert (bvule y z))
(assert (bvule z y))
(assert (= (f a) (bvmul x y)))
(assert (= (f b) (bvmul x z)))
(assert (distinct (bvmul x y) #x0000000000000000))
(check-sat)
