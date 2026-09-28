; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)

; Should fail because "a" is bound twice in the same let.
(assert (not (let ((a false) (a false)) a)))
; CHECK: Let already created:a
(check-sat)
