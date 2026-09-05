; RUN: %solver %s | %OutputCheck %s
;
; No float32 widens onto the binary64 nearest 0.1, so the equality folds
; to false at the word level.
;
; CHECK: ^unsat
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) #x3FB999999999999A)))
(check-sat)
(exit)
