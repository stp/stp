; RUN: %solver %s 2>&1 | %OutputCheck %s
; Omitting set-logic selects ALL, including floating-point operators.
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(check-sat)

; CHECK: ^sat$
