; RUN: not %solver %s 2>&1 | %OutputCheck %s
; Declarations require set-logic before any sort or term is interpreted.
(declare-const x Float64)
(check-sat)

; CHECK: error ".*is not permitted in the current solver mode"
