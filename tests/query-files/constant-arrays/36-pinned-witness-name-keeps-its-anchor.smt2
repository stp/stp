; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; Over one-bit elements the disequality fixes the store chain's witness value
; to #b0, and bit propagation states that beside its intact anchor. The value
; is one cell's, not the operand's: it must not be read as the store chain
; having become a constant array (35 is the case where it is).
(set-logic QF_ABV)
(declare-fun X () (Array (_ BitVec 4) (_ BitVec 1)))
(declare-fun i () (_ BitVec 4))
(assert (not (= ((as const (Array (_ BitVec 4) (_ BitVec 1))) #b1) (store X i #b0))))
(check-sat)
