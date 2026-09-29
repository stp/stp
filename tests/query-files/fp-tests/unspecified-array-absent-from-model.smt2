; RUN: %solver %s | %OutputCheck %s
;
; Totalising fp.to_ubv introduces an array to supply its unspecified results,
; and that array is a real array in the problem on purpose: the counterexample
; evaluator has to read a value out of it, which is why FpTotalise runs before
; the array transformer rather than at blast time.
;
; It is not the user's, though. Nothing filtered it back out at print time --
; the introduced-symbol filter only looked at entries keyed on a SYMBOL, and
; an array's entries are keyed on the READ -- so (get-model) answered with
; |@fp_unspecified_to_ubv_8x24_37_8|, a symbol never declared and in a sort
; the input's signature does not contain.
; CHECK: ^sat
; CHECK-NOT-L: @fp_unspecified
; CHECK-L: (define-fun |x| () (_ FloatingPoint 8 24)
; CHECK-NOT-L: @fp_unspecified
(set-logic QF_BVFP)
(set-option :produce-models true)
(declare-const x (_ FloatingPoint 8 24))
(assert (= ((_ fp.to_ubv 8) RNE x) #x07))
(check-sat)
(get-model)
