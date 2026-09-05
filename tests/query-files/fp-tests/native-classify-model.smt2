; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; A satisfiable pair of native classifications: the negative subnormals.
; Every sat answer is validated internally by substituting the model into
; the ORIGINAL fp.isSubnormal/fp.isNegative nodes and folding them through
; SymFPU (CheckCounterExample), so this test cross-checks a concrete native
; model against the SymFPU semantics on every run -- the check that stays
; genuinely cross-encoding now that the classifications blast natively. x
; appears twice so RemoveUnconstrained cannot discharge the predicates
; before they blast.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isSubnormal x))
(assert (fp.isNegative x))
(check-sat)
(exit)
