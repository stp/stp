; check-sat-assuming: the assumptions constrain exactly one check and leave
; the assertion stack untouched. The standard's argument is a list of
; propositional literals; any boolean formula is accepted, a superset.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun p () Bool)
(assert (= x #x1))
; A propositional literal, positive and negated.
; CHECK-NEXT: ^sat
(check-sat-assuming (p))
; CHECK-NEXT: ^sat
(check-sat-assuming ((not p)))
; Contradictory assumptions within one command.
; CHECK-NEXT: ^unsat
(check-sat-assuming (p (not p)))
; An empty assumption list is a plain check-sat.
; CHECK-NEXT: ^sat
(check-sat-assuming ())
; A formula assumption that contradicts the stack.
; CHECK-NEXT: ^unsat
(check-sat-assuming ((distinct x #x1)))
; The failed assumption is gone again: the plain check still answers sat.
; CHECK-NEXT: ^sat
(check-sat)
; And a real assertion afterwards still lands on the ordinary stack.
(assert (distinct x #x1))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
