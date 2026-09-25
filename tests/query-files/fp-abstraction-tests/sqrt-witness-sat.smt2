; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
;
; A root pinned to a constant is found through refinement and checked
; exactly.
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNormal x))
(assert (= (fp.sqrt RNE x) ((_ to_fp 8 24) #x40490fdb)))
(check-sat)
