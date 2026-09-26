; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; Lowering a distinct rebuilds the nodes above it. The term being rebuilt
; here is a Real ite, which carries no bit-vector width to restore, so the
; rebuild has to take the width-free route the Boolean case already takes.
(set-logic QF_LRA)
(declare-fun v () Real)
(assert (= 0.0 (ite (distinct 0.0 v) 0.0 1.0)))
; CHECK: ^sat
(check-sat)
