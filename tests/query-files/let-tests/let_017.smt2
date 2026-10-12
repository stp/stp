; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)

; Should fail because "a" is bound twice in the same let, even though a
; nested let sits between the two bindings.
(assert (not (let ((a false) (b (let ((c true)) c)) (a true)) a)))
; CHECK: Let already created:a
(check-sat)
