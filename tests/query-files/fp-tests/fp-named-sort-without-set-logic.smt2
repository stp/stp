; RUN: %solver %s 2>&1 | %OutputCheck %s
; Omitting set-logic selects ALL, including floating-point sorts.
(declare-const x Float64)
(check-sat)

; CHECK: ^sat$
