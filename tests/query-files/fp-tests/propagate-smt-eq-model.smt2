; RUN: %solver -p %s | %OutputCheck %s
;
; Variables eliminated by SMT-= propagation must reappear in the model
; with the values they were pinned to: the substitution map completes the
; model for symbols the formula no longer contains. (The internal
; counterexample check also validates them against the original
; assertions on every sat answer.)
;
; CHECK: ^sat
; CHECK-L: (define-fun |y| () (_ FloatingPoint 8 24) (fp #b1 #b01111111 #b10000000000000000000000))
; CHECK-L: (define-fun |x| () (_ FloatingPoint 8 24) (fp #b0 #b01111111 #b10000000000000000000000))
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= x (fp #b0 #b01111111 #b10000000000000000000000)))
(assert (= y (fp #b1 #b01111111 #b10000000000000000000000)))
(assert (fp.gt x y))
(check-sat)
(exit)
