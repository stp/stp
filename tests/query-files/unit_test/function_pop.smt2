; RUN: %solver %s | %OutputCheck %s
; Checks that popping a frame containing a function invalidates all symbols correctly
(push 1)
(declare-fun x!2 () Bool)
(define-fun x!3 () Bool (not x!2))
(pop 1)
(assert (not x!2))
; CHECK: .*error.*x!2.*
(check-sat)
