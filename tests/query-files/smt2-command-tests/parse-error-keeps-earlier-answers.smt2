; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; SMTLIB2 is a command language, so a script may legitimately have been
; answered several times before the command that broke it. Those answers stand
; and are printed as they always were; the nonzero status is the verdict on the
; run as a whole, not a retraction of what came before it.
; CHECK: ^sat$
; CHECK-NEXT: .*token: bogus.*
; CHECK-NOT: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
(check-sat)
(assert (bogus))
(assert (= x #x2))
(check-sat)
