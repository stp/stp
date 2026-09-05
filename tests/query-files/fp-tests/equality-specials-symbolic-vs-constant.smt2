; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; The specials matrix with ONE symbolic operand and one literal -- the shape
; the factory strength-reduces, and the only arrangement that reaches it.
; (Two literals fold before the rule; two symbols have no constant to
; classify against.) One (check-sat) per fact, so a failure names the arm.
;
; Each arm of the reduction is exercised against every class of symbolic
; operand:
;   fp.eq(x, NaN literal)  -> false          the NaN arm
;   fp.eq(x, +/-0 literal) -> fp.isZero(x)   the zero arm; must catch BOTH
;                                            zeros whichever zero is written
;   fp.eq(x, c)            -> (= x c)        the arm that lets equalities
;                                            propagate
; The three NaN literals differ in payload and sign, so the NaN arm is
; checked against each spelling. The zero rows are the ones that would break
; if the zero arm were ever "simplified" to a plain equality: a -0 literal
; against a +0 variable has to stay true.
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

; zero arm: +0 variable against the +0 literal
; CHECK: ^unsat
(push 1) (assert (not (fp.eq pz ((_ to_fp 8 24) #x00000000)))) (check-sat) (pop 1)

; zero arm: +0 variable against the -0 literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq pz ((_ to_fp 8 24) #x80000000)))) (check-sat) (pop 1)

; zero arm: -0 variable against the +0 literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq mz ((_ to_fp 8 24) #x00000000)))) (check-sat) (pop 1)

; zero arm: -0 variable against the -0 literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq mz ((_ to_fp 8 24) #x80000000)))) (check-sat) (pop 1)

; NaN arm: canonical quiet NaN literal
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq n1 ((_ to_fp 8 24) #x7FC00000))) (check-sat) (pop 1)

; NaN arm: payload-1 NaN literal
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq n1 ((_ to_fp 8 24) #x7F800001))) (check-sat) (pop 1)

; NaN arm: sign-set NaN literal
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq n1 ((_ to_fp 8 24) #xFFC12345))) (check-sat) (pop 1)

; NaN arm: a zero variable against a NaN literal
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq pz ((_ to_fp 8 24) #x7FC00000))) (check-sat) (pop 1)

; NaN arm: an infinity variable against a NaN literal
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq pi ((_ to_fp 8 24) #x7F800001))) (check-sat) (pop 1)

; equality arm: +oo variable against the +oo literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq pi ((_ to_fp 8 24) #x7F800000)))) (check-sat) (pop 1)

; equality arm: -oo variable against the -oo literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (fp.eq mi ((_ to_fp 8 24) #xFF800000)))) (check-sat) (pop 1)

; equality arm: infinities differ by sign
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq pi ((_ to_fp 8 24) #xFF800000))) (check-sat) (pop 1)

; equality arm: and in the other direction
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq mi ((_ to_fp 8 24) #x7F800000))) (check-sat) (pop 1)

; equality arm: infinity variable, finite literal
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq pi ((_ to_fp 8 24) #x3F800000))) (check-sat) (pop 1)

; equality arm: zero variable, finite literal
; CHECK-NEXT: ^unsat
(push 1) (assert (fp.eq pz ((_ to_fp 8 24) #x3F800000))) (check-sat) (pop 1)

; = keeps the zeros apart: +0 variable, +0 literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= pz ((_ to_fp 8 24) #x00000000)))) (check-sat) (pop 1)

; = keeps the zeros apart: +0 variable, -0 literal
; CHECK-NEXT: ^unsat
(push 1) (assert (= pz ((_ to_fp 8 24) #x80000000))) (check-sat) (pop 1)

; = keeps the zeros apart: -0 variable, +0 literal
; CHECK-NEXT: ^unsat
(push 1) (assert (= mz ((_ to_fp 8 24) #x00000000))) (check-sat) (pop 1)

; = keeps the zeros apart: -0 variable, -0 literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= mz ((_ to_fp 8 24) #x80000000)))) (check-sat) (pop 1)

; = identifies the NaNs: canonical quiet literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= n1 ((_ to_fp 8 24) #x7FC00000)))) (check-sat) (pop 1)

; = identifies the NaNs: payload-1 literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= n1 ((_ to_fp 8 24) #x7F800001)))) (check-sat) (pop 1)

; = identifies the NaNs: sign-set literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= n1 ((_ to_fp 8 24) #xFFC12345)))) (check-sat) (pop 1)

; = on infinities: +oo variable, +oo literal
; CHECK-NEXT: ^unsat
(push 1) (assert (not (= pi ((_ to_fp 8 24) #x7F800000)))) (check-sat) (pop 1)

; = on infinities: +oo variable, -oo literal
; CHECK-NEXT: ^unsat
(push 1) (assert (= pi ((_ to_fp 8 24) #xFF800000))) (check-sat) (pop 1)

; = cross-class: zero variable, NaN literal
; CHECK-NEXT: ^unsat
(push 1) (assert (= pz ((_ to_fp 8 24) #x7FC00000))) (check-sat) (pop 1)

(exit)
