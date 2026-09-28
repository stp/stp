; RUN: %solver %s | %OutputCheck %s
;
; Control for the real-literal-* unsat tests: the same equalities asserted
; positively must be satisfiable, so those tests are unsat because the
; folds agree, not because the encoding is vacuous.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RNE 1.5)))
(assert (= x ((_ to_fp 8 24) #x3fc00000)))
; CHECK: ^sat
(check-sat)
