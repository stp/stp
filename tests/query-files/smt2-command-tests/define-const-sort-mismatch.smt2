; RUN: not %solver %s | %OutputCheck %s
(set-logic QF_BV)
; CHECK: error .*define-const: the body's sort does not match
(define-const wrong Bool #b1)
