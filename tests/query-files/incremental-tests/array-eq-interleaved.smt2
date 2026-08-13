; Interleaving guard: equality rounds run as solve-local extensionality
; blocks with a fresh transformer registry, while plain-array rounds use
; the driver's persistent lazy registry. Neither may poison the other as
; the rounds alternate.
; RUN: %solver --incremental --array-equality %s | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(assert (= (select a i) #x01))
; a plain lazy-array round first
(push 1)
(assert (= (select a #x2) #x02))
(assert (= i #x2))
; a[i]=1 with i=2 contradicts a[2]=2
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
; an equality round
(push 1)
(assert (= a b))
(assert (= (select b i) #x05))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
; back to the lazy registry: the same reads as round one, reused
(push 1)
(assert (= (select a #x2) #x02))
(assert (distinct i #x2))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
; another equality round, sat this time
(push 1)
(assert (= a b))
(assert (= (select b i) #x01))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
; and a pure bit-vector finish
(push 1)
(assert (bvult i #x3))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(exit)
