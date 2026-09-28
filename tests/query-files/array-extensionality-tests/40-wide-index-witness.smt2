; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A disequality over 66-bit-index arrays: the witness index lambda is
; synthesized at the full width, the observed reads sit at 66-bit
; constant indices with the top bit exercised, and the sorted model
; extraction orders them without truncation.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 66) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 66) (_ BitVec 8)))
(assert (= (select a #b100000000000000000000000000000000000000000000000000000000000000001) #x01))
(assert (= (select a #b000000000000000000000000000000000000000000000000000000000000000010) #x02))
(assert (distinct a b))
(check-sat)
