; RUN: %solver --SMTLIB2 %s 2>&1 | %OutputCheck %s
; RUN: %solver --SMTLIB2 --lra-float-driver=1 %s 2>&1 | %OutputCheck %s
;
; The two equalities meet at a vertex whose coordinates need
; denominators near 1e18, which no double-reconstructed rational can
; carry: under the float driver the refined model has to come from the
; exact solve over the pinned bounds, not from the reconstruction.
; CHECK: ^sat
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (+ x (* 1000000007 y)) 1))
(assert (= (- (* 1000000009 x) y) 3))
(check-sat)
(exit)
