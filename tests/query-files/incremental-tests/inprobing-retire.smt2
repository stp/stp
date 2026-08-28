; REQUIRES: cadical-inprobing
; Probe-based inprocessing re-runs over the whole persistent encoding
; at every solve, so once a fixed-base session proves itself many-solve --
; and has grown a solver big enough for inprobing to cost anything -- the
; driver retires it: one bounded rebuild onto a fresh solver configured
; without it. AUTO retires only after trail reuse is gone (the floating-point
; content here sheds it at the first solve, for free), after enough solves,
; and past the size floor (each round here carries a distinct
; multiplier circuit precisely to grow the encoding; a small solver must
; NOT retire, since the rebuild would outcost the savings). Answers must
; carry straight through the restart.
; RUN: %solver --cadical -s --incremental %s 2>&1 | %OutputCheck %s
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
; CHECK: trail reuse retired
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000001))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000010))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000011))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000100))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000101))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000110))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000111))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000001000))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
; the ninth solve crosses the many-solve threshold with the size floor
; long passed: the solver restarts without inprobing
(push 1)
(assert (fp.gt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000001001))) (fp #b1 #x82 #b00000000000000000000000)))
; CHECK: inprobing retired
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.eq (fp.add RNE y (fp #b0 #x7f #b00000000000000000001010)) (fp #b0 #x7f #b00000000000000000001010)))
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
