; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; A satisfiable pair of comparisons over the SAME mux, pinning whichever
; branch the condition selects into (1.0, 2.0). Every sat answer is
; validated internally by substituting the model into the original nodes and
; folding them through SymFPU (CheckCounterExample), so this covers model
; evaluation over a surviving comparison whose operand is an ITE rather than
; a symbol -- the path a widened gate is most likely to break. The mux is
; used twice so RemoveUnconstrained cannot discharge the comparisons before
; they blast.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun c () Bool)
(assert (fp.gt (ite c x y) (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (fp.lt (ite c x y) (fp #b0 #b10000000 #b00000000000000000000000)))
(check-sat)
(exit)
