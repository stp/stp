; RUN: not %solver %s 2>&1 | %OutputCheck %s
; Declarations require set-logic before any sort or term is interpreted.
(declare-const x (_ FloatingPoint 11 53))
(check-sat)

; CHECK: error ".*is not permitted in the current solver mode"
