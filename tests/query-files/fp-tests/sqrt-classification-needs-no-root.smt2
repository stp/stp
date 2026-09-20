; A square root is NaN exactly when its operand is NaN or strictly negative,
; infinite exactly when its operand is +oo, and negative exactly when its
; operand is a negative zero -- none of which depends on the rounding mode
; or on the root. Asking only this of a root should not build one: the
; simplifying factory rewrites the classification onto the operand, and the
; whole circuit goes with it. Before the rewrite this query was 31,813
; clauses under the native encoding against SymFPU's 176, because SymFPU
; reads its flags from an unpacked record and the native result is packed.
;
; RUN: %solver --bb.fp-native-sqrt=true --output-CNF --exit-after-CNF %s 2>&1 | %OutputCheck %s
; RUN: %solver --bb.fp-native-sqrt=false %s 2>&1 | %OutputCheck --check-prefix=ANS %s
; RUN: %solver --bb.fp-native-sqrt=true %s 2>&1 | %OutputCheck --check-prefix=ANS %s
;
; CHECK-NOT: ERROR
; ANS: ^unsat
;
(set-logic QF_FP)
(declare-fun x () Float64)
(declare-fun y () Float64)
(assert (= y (fp.sqrt RNE x)))
; x is a positive normal, so its root is neither NaN, nor infinite, nor
; negative -- asserting any of the three is unsatisfiable.
(assert (fp.isNormal x))
(assert (fp.isPositive x))
(assert (or (fp.isNaN y) (fp.isInfinite y) (fp.isNegative y)))
(check-sat)
(exit)
