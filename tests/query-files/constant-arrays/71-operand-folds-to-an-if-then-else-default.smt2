; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality -d %s | %OutputCheck %s
; As 70, with a default that is an if-then-else: the folded anchor reads
; "name = (ite (bvult x y) x y)". The recovery took any if-then-else equated
; with a witness name for the witness read distributed over an array
; if-then-else, and reported that, although the read had not been
; distributed but folded. For an operand built over a constant array, a term
; that mentions no witness symbol is no anchor but the default of the constant
; array the operand has become.
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(assert (= (bvand y #x1) #x1))
(assert (= (ite (= ((_ extract 0 0) y) #b1)
                ((as const (Array (_ BitVec 4) (_ BitVec 4))) (ite (bvult x y) x y))
                a)
           ((as const (Array (_ BitVec 4) (_ BitVec 4))) y)))
; CHECK: ^sat$
(check-sat)
; The defaults are then x and y, and x < y makes them differ.
(assert (bvult x y))
; CHECK: ^unsat$
(check-sat)
