; Not specific to one option: every option whose argument is a <b_value>
; (SMT-LIB 2.6, figure 3.9) answers a malformed value the same way, with an
; error response rather than "unsupported" -- which is reserved for what the
; solver cannot do (3.9.1). One option per file, because the error stops the
; run; global-declarations-bad-value covers :global-declarations.
; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error ".*:produce-models takes true or false.*yes"\)$
(set-option :produce-models yes)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
; CHECK-NOT: ^sat$
(check-sat)
