; Arrays inside the incremental driver: lazy read-congruence refinement on
; the persistent solver, canonical read abstractions reused across rounds,
; and store chains resolved by the transform.
; RUN: %solver --incremental %s | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(assert (= (select a i) #x01))
(push 1)
; aliased indices with different values force a congruence axiom
(assert (= (select a j) #x02))
(assert (= i j))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(push 1)
; the same read returns after the pop, distinct indices this time
(assert (= (select a j) #x02))
(assert (distinct i j))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
; CHECK-NEXT: ^sat
(check-sat)
(push 1)
; read-over-write: a store must shadow the stored index...
(assert (= (select (store a i #x07) i) #x08))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(push 1)
; ...and pass reads through at other indices
(assert (distinct i j))
(assert (= (select (store a j #x07) i) #x01))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
; the base level can grow an array constraint between rounds
(assert (= (select a #x30) #x33))
(push 1)
(assert (= i #x30))
; a[i]=1 but a[0x30]=0x33, so i cannot be 0x30
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert (= j #x30))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(exit)
