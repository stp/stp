; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; An array ITE equated with its own then-branch reduces to the condition
; or the else-branch's equality. With the condition denied, the branches
; must be pointwise equal, contradicting the differing cell.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun c () Bool)
(declare-fun k () (_ BitVec 8))
(assert (= (ite c a b) a))
(assert (not c))
(assert (distinct (select a k) (select b k)))
(check-sat)
