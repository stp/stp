; RUN: not %solver %s 2>&1 | %OutputCheck %s
; RUN: not %solver %s 2>&1 | %OutputCheck --check-prefix=NOANSWER %s
;
; ALL is the most common logic STP does not decide -- 4,552 of the 16,905
; files in the local corpus name it -- and it is the one name that is a
; logic without being built out of theory abbreviations. It is reported as
; a logic STP is missing, not as a name nobody has heard of.
; CHECK-L: unsupported logic: STP decides
; CHECK-L: token: ALL
; NOANSWER-NOT: ^sat$
; NOANSWER-NOT: ^unsat$
(set-logic ALL)
(declare-fun p () Bool)
(assert p)
(check-sat)
(exit)
