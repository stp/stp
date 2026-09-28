; RUN: %solver --SMTLIB2 --lra-presolve-unconstrained=1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; Unconstrained elimination: x occurs in exactly one atom at a pure
; polarity, so the atom folds to its polarity's truth and the witness
; equality realising it is conjoined -- the model stays complete, and
; get-value on the witnessed variable must satisfy the folded atom.
; CHECK: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun r () Bool)
(push 1)
(assert (or (<= x 5) r))
(assert (not r))
(check-sat)
(pop 1)
(push 1)
(assert (not (< y 5)))
(assert (>= z 3))
(assert (<= z 2))
(check-sat)
(pop 1)
(assert (> y 7))
(check-sat)
(exit)
