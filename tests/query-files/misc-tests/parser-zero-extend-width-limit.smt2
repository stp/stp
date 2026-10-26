; A zero_extend whose width passes 2^32 - 1, which wrapped in 32 bits.

; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "syntax error: line [0-9]+ a bit-vector is at most 4294967295 bits wide

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= ((_ zero_extend 4294967295) x) #b0000000))
(check-sat)
