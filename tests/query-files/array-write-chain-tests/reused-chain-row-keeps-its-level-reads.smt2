; RUN: %solver --incremental=on %s | %OutputCheck %s
; RUN: %solver --incremental=on -d %s | %OutputCheck %s
; RUN: %solver --incremental=on --lazy-write-reads=0 %s | %OutputCheck %s
; RUN: %solver --incremental=off %s | %OutputCheck %s
; Enough reads over write chains to have the chain abstracted to refinement
; rows, under one push level, then a read of the same cell under the next,
; after a pop. The chain stores reads -- a read of the base array, then a
; read over a second abstracted chain -- below the levels a read expands
; eagerly, so the abstracted row's levels mention their read rows. The
; incremental solver seeds refinement with the rows each assumed conjunct
; touches. A conjunct that reused the row from the registry touched the
; row and its fall-through read, but not the rows its levels mention: only
; the conjunct that built the row did, and it was popped. Those rows then
; took no congruence axioms, the read the model needs floated, and the
; solver aborted with "an array refinement round rejected the candidate
; but emitted no new logical axiom".
; CHECK: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^sat$
(set-logic QF_ABV)
(declare-fun s1 () (_ BitVec 8))
(declare-fun s2 () (_ BitVec 8))
(declare-fun s3 () (_ BitVec 8))
(declare-fun s4 () (_ BitVec 8))
(declare-fun p3 () (_ BitVec 8))
(declare-fun p4 () (_ BitVec 8))

; The levels store reads of the base array.
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(define-fun w () (Array (_ BitVec 8) (_ BitVec 8))
  (store (store (store (store a s4 (select a p4)) s3 (select a p3))
    s2 #x02) s1 #x01))
(assert (= (select a #x0c) #x05))
(push 1)
(assert (distinct (select w #x01) #x63))
(assert (distinct (select w #x02) #x63))
(assert (distinct (select w #x03) #x63))
(assert (distinct (select w #x04) #x63))
(assert (distinct (select w #x0c) #x09))
(check-sat)
(pop 1)
(push 1)
; Neither the eager levels nor the base cell holds #x07, so a model takes
; it from a stored read.
(assert (= (select w #x0c) #x07))
(check-sat)
(pop 1)

; The levels store reads over a second abstracted chain, one of them at an
; index that is itself a read.
(declare-fun t1 () (_ BitVec 8))
(declare-fun t2 () (_ BitVec 8))
(declare-fun t3 () (_ BitVec 8))
(declare-fun t4 () (_ BitVec 8))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(define-fun u () (Array (_ BitVec 8) (_ BitVec 8))
  (store (store (store (store b t4 #x0b) t3 #x0a) t2 #x02) t1 #x01))
(define-fun v () (Array (_ BitVec 8) (_ BitVec 8))
  (store (store (store (store b s4 (select u p4))
    s3 (select u (bvadd (select b p3) #x01))) s2 #x02) s1 #x01))
(assert (= (select b #x0c) #x05))
(push 1)
(assert (distinct (select u #x01) #x63))
(assert (distinct (select u #x02) #x63))
(assert (distinct (select u #x03) #x63))
(assert (distinct (select u #x04) #x63))
(assert (distinct (select u #x05) #x63))
(assert (distinct (select v #x01) #x63))
(assert (distinct (select v #x02) #x63))
(assert (distinct (select v #x0c) #x09))
(check-sat)
(pop 1)
(push 1)
(assert (= (select v #x0c) #x07))
(check-sat)
(pop 1)
