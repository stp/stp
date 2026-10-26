; (_ extract i j) needs i >= j. With j = i + 1 the width came out as 0,
; which the "negative width" check let through, and the zero-width term
; ended in an internal error (an assertion in assertion builds).

; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "syntax error: line [0-9]+ extract's top index is below its bottom index

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= ((_ extract 0 1) x) ((_ extract 3 4) x)))
(check-sat)
