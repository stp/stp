; RUN: not %solver %s 2>&1 | %OutputCheck %s
; RUN: not %solver %s 2>&1 | %OutputCheck --check-prefix=NOANSWER %s
;
; QF_LIA is a logic; it is not one STP decides. Refusing it ends the session,
; which is what STP has always answered (get-info :error-behavior) with.
; Continuing was the one place that answer was untrue: the refusal went out,
; the script ran on, and the check-sat below reported a verdict for a
; benchmark STP had just said it could not accept. Over a local corpus of
; 16,905 files naming a logic STP does not decide, 672 were answered that
; way -- 344 of them "unsat".
;
; The name is reported as a logic STP does not have, not as a name that is
; not a logic: those are different mistakes and the diagnostic says which.
; CHECK-L: unsupported logic: STP decides
; CHECK-L: token: QF_LIA
; NOANSWER-NOT: ^sat$
; NOANSWER-NOT: ^unsat$
(set-logic QF_LIA)
(declare-fun p () Bool)
(assert p)
(check-sat)
(exit)
