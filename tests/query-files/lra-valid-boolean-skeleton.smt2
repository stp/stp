; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; A tautology over Real atoms. The Boolean skeleton is valid, so simplification
; folds it away and no atom reaches the CNF at all -- every opaque atom is then
; legitimately unbound. The coordinator used to decide that by asking whether
; the atom occurred in the frontend's output, which predates the
; simplification, so it read the absent binding as a mapping fault and the
; caller got an error where the answer is plainly sat.
; CHECK-NEXT: ^sat$
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (=> (>= y x) (=> (< y 1.0) (=> (< y 1.0) (>= y x)))))
(check-sat)
(exit)
