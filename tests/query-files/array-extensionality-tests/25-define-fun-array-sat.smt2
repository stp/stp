; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A nullary array-sorted define-fun expands to its body at every use:
; the element reads see the stored values through the chain, and the
; whole-array disequality with the base is satisfied by choosing base
; contents that differ from a written value.
(set-logic QF_ABV)
(declare-fun base () (Array (_ BitVec 2) (_ BitVec 2)))
(define-fun A0 () (Array (_ BitVec 2) (_ BitVec 2)) (store (store base #b00 #b01) #b10 #b11))
(assert (= (select A0 #b00) #b01))
(assert (= (select A0 #b10) #b11))
(assert (distinct A0 base))
(check-sat)
