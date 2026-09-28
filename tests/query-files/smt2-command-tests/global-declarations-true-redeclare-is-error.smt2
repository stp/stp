; The mirror image of global-declarations-false-redeclare-after-pop: when the
; declaration survives the pop, reusing the name is a redeclaration, and
; SMT-LIB 2.6 section 4.2.1 forbids declaring a symbol that is already in scope.
; Accepting this script under both settings of the option is the bug that makes
; the two settings indistinguishable.
; RUN: not %solver %s | %OutputCheck %s
(set-option :global-declarations true)
(set-logic QF_BV)
(push 1)
(declare-fun x!0 () Bool)
(assert (not x!0))
; CHECK: ^sat$
(check-sat)
(pop 1)
(push 1)
; CHECK: .*error.*token: x!0.*
(declare-fun x!0 () (_ BitVec 32))
(assert (= x!0 (_ bv0 32)))
(check-sat)
