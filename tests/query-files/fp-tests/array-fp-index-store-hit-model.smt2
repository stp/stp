; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A store at a symbolic NaN index is hit by a select at a NaN literal
; of a different payload: the two indexes denote the one NaN. Model
; evaluation used to compare the interned float literal against the
; plain bits the canonicalized store index evaluates to by node
; identity, "miss" the write, and re-check candidate models against a
; wrong value.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (bvugt (select (store a x #x11) (fp #b0 #b11111111 #b00000000000000000000001)) #x10))
(assert (bvult (select (store a x #x11) (fp #b0 #b11111111 #b00000000000000000000001)) #x12))
(check-sat)
