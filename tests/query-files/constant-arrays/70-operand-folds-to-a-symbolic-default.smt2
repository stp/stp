; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality -d %s | %OutputCheck %s
; The low bit of y is set, which preprocessing finds only after the equality
; has been lowered, so the if-then-else becomes its constant-array branch
; there, and the witness read over it folds to the default: the anchor
; "name = read(operand, lambda)" is left as "name = x". The recovery of an
; operand that became a constant array took a value only when it was a
; constant (35), so a symbolic default left the operand reported lost, an
; internal error in both drivers. The operand is the constant array of x.
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(assert (= (bvand y #x1) #x1))
(assert (= (ite (= ((_ extract 0 0) y) #b1)
                ((as const (Array (_ BitVec 4) (_ BitVec 4))) x)
                a)
           ((as const (Array (_ BitVec 4) (_ BitVec 4))) y)))
; CHECK: ^sat$
(check-sat)
(assert (not (= x y)))
; CHECK: ^unsat$
(check-sat)
