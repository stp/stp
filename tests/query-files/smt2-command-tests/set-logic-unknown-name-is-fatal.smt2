; RUN: not %solver %s 2>&1 | %OutputCheck %s
; RUN: not %solver %s 2>&1 | %OutputCheck --check-prefix=NOANSWER %s
;
; NOSUCHLOGIC is not a logic STP is missing, it is not a logic at all: no
; SMT-LIB name is built this way. Same refusal, same exit, different
; diagnostic -- the two are the two mistakes a set-logic can make, and a
; caller that typed a name wrong is not told to go and read the list of
; logics STP does not implement.
; CHECK-L: unknown logic: SMT-LIB names no logic this way
; CHECK-L: token: NOSUCHLOGIC
; NOANSWER-NOT: ^sat$
; NOANSWER-NOT: ^unsat$
(set-logic NOSUCHLOGIC)
(declare-fun p () Bool)
(assert p)
(check-sat)
(exit)
