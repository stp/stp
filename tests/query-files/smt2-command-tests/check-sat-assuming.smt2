; check-sat-assuming parses and answers "unsupported". The standard's argument
; is a list of propositional literals, which is what must be accepted here; an
; empty list is legal too.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun p () Bool)
(assert (= x #x1))
; CHECK-NEXT: ^unsupported
(check-sat-assuming (p))
; CHECK-NEXT: ^unsupported
(check-sat-assuming ((not p)))
; CHECK-NEXT: ^unsupported
(check-sat-assuming (p (not p)))
; CHECK-NEXT: ^unsupported
(check-sat-assuming ())
; CHECK-NEXT: ^sat
(check-sat)
