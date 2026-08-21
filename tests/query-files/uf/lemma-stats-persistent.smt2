; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^UF: installed congruence lemma 1 for f \(block guarded\)$
; CHECK: ^unsat$
; CHECK-NOT: installed congruence lemma 2
; UF2-INC-02: the persistent form of the same refinement carries the
; exact-stack block guard, and -s names the host. --uf-ackermann=off keeps
; the lemma dynamic; eagerly encoded, this query would install none.
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
