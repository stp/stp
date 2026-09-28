; RUN: %solver %s | %OutputCheck %s
;
; An exactly representable literal rounds the same under every mode, so
; even with a free rounding mode the conversion collapses to the one
; constant (no ite is built at all) and nothing can make it differ.
(set-logic QF_FP)
(declare-const r RoundingMode)
(declare-const x (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) r 1.5)))
(assert (distinct x ((_ to_fp 8 24) #x3fc00000)))
; CHECK: ^unsat
(check-sat)
