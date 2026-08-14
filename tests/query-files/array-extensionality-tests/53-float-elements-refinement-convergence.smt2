; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A float constant interns separately from the bitvector constant with
; the same bits, but the consistency checker compares model constants
; by node identity. A float-constant write value kept in the access
; graph as itself therefore never compared equal to the same bits read
; back from the SAT assignment, and refinement re-reported the same
; phantom conflict forever: this query (found by differential fuzzing)
; ran tens of thousands of lemma iterations without terminating before
; constants entering the graph and the checker's model view were
; canonicalized to the plain bitvector flavour.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(declare-fun b () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(declare-fun c () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= (ite (not (fp.eq ((_ to_fp 8 24) #x00000000) x)) (store b #b00 ((_ to_fp 8 24) #x7F800000)) (store a #b10 ((_ to_fp 8 24) #xFF800000))) (store (store b #b10 ((_ to_fp 8 24) #x5B7D8377)) #b11 (select a #b10))))
(assert (fp.eq x x))
(assert (distinct (store b #b10 (ite (not (= c a)) y ((_ to_fp 8 24) #x7FC00000))) b))
(check-sat)
