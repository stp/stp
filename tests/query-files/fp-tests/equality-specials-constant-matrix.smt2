; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; The specials matrix written as LITERALS, so it lands on the constant path
; -- the node-creation folders and the constant evaluator -- rather than on a
; blasted circuit. Both operators, one (check-sat) per fact.
;
; The NaN rows are the reason this exists as a separate file: three different
; NaN bit patterns are used (canonical quiet, a payload-1 pattern with the
; quiet bit clear, and one with the sign bit set and another payload). All
; three denote the single SMT-LIB NaN, so `=` must hold between any two and
; fp.eq between none. A constant path that compared packed bits, or that let
; a payload survive interning, gets these backwards -- and no symbolic test
; can catch it, because the two spellings only ever meet as constants here.
;
(set-logic QF_FP)
(declare-fun unused () Bool)

; fp.eq: the zero literals are numerically equal
; CHECK: ^unsat
(push 1) (assert (not (fp.eq ((_ to_fp 8 24) #x00000000) ((_ to_fp 8 24) #x80000000)))) (check-sat) (pop 1)

; fp.eq: and in the other operand order
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq ((_ to_fp 8 24) #x80000000) ((_ to_fp 8 24) #x00000000)))) (check-sat) (pop 1)

; fp.eq: +oo literal against itself
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #x7F800000)))) (check-sat) (pop 1)

; fp.eq: -oo literal against itself
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq ((_ to_fp 8 24) #xFF800000) ((_ to_fp 8 24) #xFF800000)))) (check-sat) (pop 1)

; fp.eq: the infinity literals differ by sign
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #xFF800000))) (check-sat) (pop 1)

; fp.eq: a NaN literal is not equal to itself
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x7FC00000))) (check-sat) (pop 1)

; fp.eq: nor to a different NaN bit pattern
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x7F800001))) (check-sat) (pop 1)

; fp.eq: nor across payload AND sign
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq ((_ to_fp 8 24) #x7F800001) ((_ to_fp 8 24) #xFFC12345))) (check-sat) (pop 1)

; fp.eq: NaN literal against a zero literal
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x00000000))) (check-sat) (pop 1)

; fp.eq: infinity literal against a finite one
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #x3F800000))) (check-sat) (pop 1)

; =: the zero literals are two different values
; CHECK-NEXT: ^unsat
(push 1) (assert (= ((_ to_fp 8 24) #x00000000) ((_ to_fp 8 24) #x80000000))) (check-sat) (pop 1)

; =: and in the other operand order
; CHECK-NEXT: ^unsat
(push 1) (assert (= ((_ to_fp 8 24) #x80000000) ((_ to_fp 8 24) #x00000000))) (check-sat) (pop 1)

; =: +oo literal against itself
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #x7F800000)))) (check-sat) (pop 1)

; =: -oo literal against itself
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= ((_ to_fp 8 24) #xFF800000) ((_ to_fp 8 24) #xFF800000)))) (check-sat) (pop 1)

; =: the infinity literals differ by sign
; CHECK-NEXT: ^unsat
(push 1) (assert (= ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #xFF800000))) (check-sat) (pop 1)

; =: a NaN literal equals itself
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x7FC00000)))) (check-sat) (pop 1)

; =: and a different NaN bit pattern (interning)
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x7F800001)))) (check-sat) (pop 1)

; =: and across payload AND sign
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= ((_ to_fp 8 24) #x7F800001) ((_ to_fp 8 24) #xFFC12345)))) (check-sat) (pop 1)

; =: and in the other operand order
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= ((_ to_fp 8 24) #xFFC12345) ((_ to_fp 8 24) #x7FC00000)))) (check-sat) (pop 1)

; =: NaN literal against a zero literal
; CHECK-NEXT: ^unsat
(push 1) (assert (= ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x00000000))) (check-sat) (pop 1)

; =: infinity literal against a finite one
; CHECK-NEXT: ^unsat
(push 1) (assert (= ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #x3F800000))) (check-sat) (pop 1)

(exit)
