; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
;
; x / x = 1 for every finite nonzero x, an identity rule of the divider's
; abstraction.
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNormal x))
(assert (not (= (fp.div RNE x x) ((_ to_fp 8 24) #x3f800000))))
(check-sat)
