; RUN: %solver %s 2>&1 | %OutputCheck %s
; Omitting set-logic selects ALL, including floating-point sorts.
(declare-const x (_ FloatingPoint 11 53))
(check-sat)

; CHECK: ^sat$
