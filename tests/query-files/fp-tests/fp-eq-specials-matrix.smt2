; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; fp.eq over the matrix of special values, pairwise, one (check-sat) per
; fact so that a failure names the row rather than the file. The operands
; are symbolic and pinned by classification, so each is free to be any
; witness of its class -- in particular the two NaNs may take different
; payloads and different signs -- and every row has to hold for every
; choice.
;
; fp.eq is IEEE numeric equality: the two zeros are numerically equal, NaN
; is equal to nothing, and infinities agree exactly when their signs do.
; Each row is probed on its own, in the polarity that makes it unsat.
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

; the two zeros are numerically equal
; CHECK: ^unsat
(push 1) (assert (not (fp.eq pz mz))) (check-sat) (pop 1)

; +0 against itself
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq pz pz))) (check-sat) (pop 1)

; -0 against itself
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq mz mz))) (check-sat) (pop 1)

; and in the other operand order
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq mz pz))) (check-sat) (pop 1)

; NaN is equal to nothing, itself included
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq n1 n1)) (check-sat) (pop 1)

; nor to a second NaN, of any payload or sign
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq n1 n2)) (check-sat) (pop 1)

; nor in the other operand order
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq n2 n1)) (check-sat) (pop 1)

; +oo equals +oo
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq pi pi))) (check-sat) (pop 1)

; -oo equals -oo
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq mi mi))) (check-sat) (pop 1)

; but the infinities differ by sign
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq pi mi)) (check-sat) (pop 1)

; and in the other operand order
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq mi pi)) (check-sat) (pop 1)

; NaN against a zero
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq n1 pz)) (check-sat) (pop 1)

; NaN against an infinity
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq n1 pi)) (check-sat) (pop 1)

; NaN against a finite value
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq n1 one)) (check-sat) (pop 1)

; an infinity against a zero
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq pi pz)) (check-sat) (pop 1)

; an infinity against a finite value
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq pi one)) (check-sat) (pop 1)

; a zero against a finite value
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq pz one)) (check-sat) (pop 1)

(exit)
