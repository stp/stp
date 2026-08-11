; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The same two writes over one base in swapped order, with symbolic
; indexes asserted distinct: extensionally equal, so denying the
; equality is unsatisfiable. The chains share a base but not a common
; write prefix, so the equality stays opaque and the witness
; machinery's refinement decides it.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (distinct i j))
(assert (distinct (store (store a i v) j w) (store (store a j w) i v)))
(check-sat)
