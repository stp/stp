; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; A satisfiable pair of native comparisons pinning x into (1.0, 2.0). Every
; sat answer is validated internally by substituting the model into the
; ORIGINAL fp.gt/fp.lt nodes and folding them through SymFPU
; (CheckCounterExample), so this test cross-checks a concrete native model
; against the SymFPU semantics on every run. x appears twice so
; RemoveUnconstrained cannot discharge the comparisons before they blast.
; The (fp ...) literal spelling interns at parse, keeping the operands leaves
; even under --disable-simplifications.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.gt x (fp #b0 #b01111111 #b00000000000000000000000))) ; x > 1.0
(assert (fp.lt x (fp #b0 #b10000000 #b00000000000000000000000))) ; x < 2.0
(check-sat)
(exit)
