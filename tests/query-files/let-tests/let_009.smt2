; RUN: %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)

; CHECK-NOT:"sat"
; Should fail because binds "a" twice in the same let.
;(assert (not (let ((a false) (a false)) a)))

(check-sat)