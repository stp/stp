; A concat whose width passes 2^32 - 1. The sum was taken in 32 bits, so
; 2^31 + (2^31 + 1) bits became a 1-bit term, the type check summed the
; same way and agreed, and this answered sat: bit 0 of the concat is bit 0
; of y, asserted both 1 and 0.

; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "syntax error: line [0-9]+ a bit-vector is at most 4294967295 bits wide
; CHECK-NOT: ^sat

(set-logic QF_BV)
(declare-fun x () (_ BitVec 2147483648))
(declare-fun y () (_ BitVec 2147483649))
(assert (= ((_ extract 0 0) (concat x y)) #b1))
(assert (= ((_ extract 0 0) y) #b0))
(check-sat)
