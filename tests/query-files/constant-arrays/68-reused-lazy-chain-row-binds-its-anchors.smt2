; RUN: %solver --incremental=on --lazy-write-reads=1 --lazy-write-reads-depth=2 %s | %OutputCheck %s
; RUN: %solver --incremental=on --lazy-write-reads=1 --lazy-write-reads-depth=2 -d %s | %OutputCheck %s
; RUN: %solver --incremental=on --lazy-write-reads=0 %s | %OutputCheck %s
; RUN: %solver --incremental=off --lazy-write-reads=1 --lazy-write-reads-depth=2 %s | %OutputCheck %s
; Reads at symbolic indexes over a write chain on a constant array, enough
; of them to be abstracted to refinement rows, first under one push level
; and then, after a pop, under the next. A row's computed terms -- here the
; default, then a stored value -- are carried by anchor variables, and an
; anchor's binding equation was conjoined only by the conjunct that minted
; it. The incremental solver re-binds the anchors of every row a later
; conjunct reuses, but not the default's, and not at all for a conjunct
; that touches no read row, which a chain over a constant array never
; does. Under the second level the anchor floated, refinement could not
; refute the candidate, and the solver aborted with "an array refinement
; round rejected the candidate but emitted no new logical axiom".
(set-logic QF_ABV)
(declare-fun i0 () (_ BitVec 8))
(declare-fun i1 () (_ BitVec 8))
(declare-fun i2 () (_ BitVec 8))
(declare-fun i3 () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(declare-fun j0 () (_ BitVec 8))
(declare-fun j1 () (_ BitVec 8))
(declare-fun j2 () (_ BitVec 8))
(declare-fun j3 () (_ BitVec 8))
(declare-fun j4 () (_ BitVec 8))

; A computed default: every cell is #x02 or z+1.
(define-fun a () (Array (_ BitVec 8) (_ BitVec 8))
  (store (store (store (store
    ((as const (Array (_ BitVec 8) (_ BitVec 8))) (bvadd z #x01))
    i0 #x02) i1 #x02) i2 #x02) i3 #x02))
(push 1)
(assert (or (= (select a j0) #x05) (= (select a j1) #x05)
            (= (select a j2) #x05) (= (select a j3) #x05)
            (= (select a j4) #x05)))
; CHECK: ^sat$
(check-sat)
(pop 1)
(push 1)
; z+5 is never z+1, and is #x02 only at z = #xfd.
(assert (distinct z #xfd))
(assert (or (= (select a j0) (bvadd z #x05)) (= (select a j1) (bvadd z #x05))
            (= (select a j2) (bvadd z #x05)) (= (select a j3) (bvadd z #x05))
            (= (select a j4) (bvadd z #x05))))
; CHECK: ^unsat$
(check-sat)
(pop 1)

; A computed stored value: every cell is #x01 or z+2.
(define-fun b () (Array (_ BitVec 8) (_ BitVec 8))
  (store (store (store (store
    ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x01)
    i0 (bvadd z #x02)) i1 (bvadd z #x02)) i2 (bvadd z #x02)) i3 (bvadd z #x02)))
(push 1)
(assert (or (= (select b j0) #x05) (= (select b j1) #x05)
            (= (select b j2) #x05) (= (select b j3) #x05)
            (= (select b j4) #x05)))
; CHECK: ^sat$
(check-sat)
(pop 1)
(push 1)
; z+7 is never z+2, and is #x01 only at z = #xfa.
(assert (distinct z #xfa))
(assert (or (= (select b j0) (bvadd z #x07)) (= (select b j1) (bvadd z #x07))
            (= (select b j2) (bvadd z #x07)) (= (select b j3) (bvadd z #x07))
            (= (select b j4) (bvadd z #x07))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
