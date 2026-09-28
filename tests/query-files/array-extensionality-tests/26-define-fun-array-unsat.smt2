; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Two defined names carrying the same two writes in commuted order
; over one base, at provably distinct constant indices: extensionally
; equal, so the whole-array distinct is unsatisfiable. The defined
; names must expand into genuine equality-abstraction operands for the
; refinement lemmas to see the write chains.
(set-logic QF_ABV)
(declare-fun base () (Array (_ BitVec 2) (_ BitVec 2)))
(define-fun A0 () (Array (_ BitVec 2) (_ BitVec 2)) (store (store base #b00 #b01) #b10 #b11))
(define-fun A1 () (Array (_ BitVec 2) (_ BitVec 2)) (store (store base #b10 #b11) #b00 #b01))
(assert (distinct A0 A1))
(check-sat)
