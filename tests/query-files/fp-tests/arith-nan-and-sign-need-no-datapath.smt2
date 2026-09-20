; Whether an arithmetic result is NaN is a question about the operands'
; classes, and the sign of a product or a quotient is the exclusive-or of
; its operands' signs. Neither needs the datapath, and the native encodings
; pack their result, so without a rewrite a query asking only this carried
; the whole adder, multiplier or divider into the CNF: at float32 the NaN
; test of a product was 10,449 clauses and of a quotient 14,508.
;
; isInfinite and isZero get no such rule: overflow and underflow genuinely
; need the arithmetic, and a sum's sign cancels.
;
; RUN: %solver --output-CNF --exit-after-CNF %s 2>&1 | %OutputCheck %s
; RUN: %solver %s 2>&1 | %OutputCheck --check-prefix=ANS %s
; RUN: %solver --bb.fp-native-arith=0 --bb.fp-native-div=0 %s 2>&1 | %OutputCheck --check-prefix=ANS %s
;
; CHECK-NOT: ERROR
; ANS: ^unsat
;
(set-logic QF_FP)
(declare-fun a () Float32)
(declare-fun b () Float32)
(declare-fun p () Float32)
(declare-fun q () Float32)
(declare-fun s () Float32)
(assert (= p (fp.mul RNE a b)))
(assert (= q (fp.div RNE a b)))
(assert (= s (fp.add RNE a b)))
; both operands are positive normals, so no operation here is invalid and
; no result is negative
(assert (fp.isNormal a))
(assert (fp.isPositive a))
(assert (fp.isNormal b))
(assert (fp.isPositive b))
(assert (or (fp.isNaN p) (fp.isNaN q) (fp.isNaN s)
            (fp.isNegative p) (fp.isNegative q)))
(check-sat)
(exit)
