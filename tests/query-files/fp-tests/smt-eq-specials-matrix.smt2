; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; SMT-LIB `=` over the matrix of special values, pairwise, one (check-sat)
; per fact -- the companion to fp-eq-specials-matrix.smt2. The two operators
; disagree on exactly the zero and NaN rows, and running the same matrix
; through both is what pins that difference down.
;
; `=` is equality on the abstract FloatingPoint domain: +0 and -0 are
; DISTINCT values, there is ONE NaN so any two NaNs are equal whatever
; payloads and signs the solver picks (the both-NaN disjunct of the native
; BBeqFP encoding -- comparing packed bits alone fails this), and infinities
; agree exactly when their signs do.
;
(set-logic QF_FP)
(declare-fun pz () (_ FloatingPoint 8 24))
(declare-fun mz () (_ FloatingPoint 8 24))
(declare-fun pi () (_ FloatingPoint 8 24))
(declare-fun mi () (_ FloatingPoint 8 24))
(declare-fun n1 () (_ FloatingPoint 8 24))
(declare-fun n2 () (_ FloatingPoint 8 24))
(declare-fun one () (_ FloatingPoint 8 24))
(assert (and (fp.isZero pz) (fp.isPositive pz)))
(assert (and (fp.isZero mz) (fp.isNegative mz)))
(assert (and (fp.isInfinite pi) (fp.isPositive pi)))
(assert (and (fp.isInfinite mi) (fp.isNegative mi)))
(assert (fp.isNaN n1))
(assert (fp.isNaN n2))
(assert (= one ((_ to_fp 8 24) #x3F800000)))

; +0 against itself
; CHECK: ^unsat
(push 1) (assert (not (= pz pz))) (check-sat) (pop 1)

; -0 against itself
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= mz mz))) (check-sat) (pop 1)

; the signed zeros are two DIFFERENT values
; CHECK-NEXT: ^unsat
(push 1) (assert (= pz mz)) (check-sat) (pop 1)

; and in the other operand order
; CHECK-NEXT: ^unsat
(push 1) (assert (= mz pz)) (check-sat) (pop 1)

; one NaN value: a NaN equals itself
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= n1 n1))) (check-sat) (pop 1)

; and a second NaN, whatever payload and sign
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= n1 n2))) (check-sat) (pop 1)

; and in the other operand order
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= n2 n1))) (check-sat) (pop 1)

; +oo equals +oo
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= pi pi))) (check-sat) (pop 1)

; -oo equals -oo
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= mi mi))) (check-sat) (pop 1)

; but the infinities differ by sign
; CHECK-NEXT: ^unsat
(push 1) (assert (= pi mi)) (check-sat) (pop 1)

; and in the other operand order
; CHECK-NEXT: ^unsat
(push 1) (assert (= mi pi)) (check-sat) (pop 1)

; NaN against a zero
; CHECK-NEXT: ^unsat
(push 1) (assert (= n1 pz)) (check-sat) (pop 1)

; NaN against an infinity
; CHECK-NEXT: ^unsat
(push 1) (assert (= n1 pi)) (check-sat) (pop 1)

; NaN against a finite value
; CHECK-NEXT: ^unsat
(push 1) (assert (= n1 one)) (check-sat) (pop 1)

; an infinity against a zero
; CHECK-NEXT: ^unsat
(push 1) (assert (= pi pz)) (check-sat) (pop 1)

; an infinity against a finite value
; CHECK-NEXT: ^unsat
(push 1) (assert (= pi one)) (check-sat) (pop 1)

; a zero against a finite value
; CHECK-NEXT: ^unsat
(push 1) (assert (= pz one)) (check-sat) (pop 1)

(exit)
