; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
; RUN: %solver -r %s | %OutputCheck %s
;
; A satisfiable pair of native comparisons over a select, pinning the cell
; into (1.0, 2.0). Every sat answer is validated internally by substituting
; the model into the original nodes and folding them through SymFPU
; (CheckCounterExample), so this covers model evaluation over a surviving
; comparison whose operand is an array read -- the counterexample path runs
; after the array machinery has rewritten that operand. The same select is
; used twice so RemoveUnconstrained cannot discharge the comparisons.
;
; CHECK: ^sat
(set-logic QF_ABVFP)
(declare-fun A () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun i () (_ BitVec 4))
(assert (fp.gt (select A i) (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (fp.lt (select A i) (fp #b0 #b10000000 #b00000000000000000000000)))
(check-sat)
(exit)
