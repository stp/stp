; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; distinct over operands the node factory can settle by itself. It hands back
; the Boolean answer rather than an equality to normalize, which the pairwise
; expansion has to answer directly instead of passing on as a comparison.
(set-logic QF_LRA)
(assert (distinct 0.0 1.0))
; CHECK: ^sat
(check-sat)
