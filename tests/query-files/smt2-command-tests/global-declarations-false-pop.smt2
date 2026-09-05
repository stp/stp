; :global-declarations false is the option's required default (SMT-LIB 2.6,
; section 4.1.7): declarations belong to the assertion level that made them, so
; popping that level takes the name out of scope again.
; RUN: not %solver %s | %OutputCheck %s
(set-option :global-declarations false)
(set-logic QF_BV)
(push 1)
(declare-fun x!1 () Bool)
(define-fun x!2 () Bool (not x!1))
(pop 1)
; STP's :error-behavior is immediate-exit, so this is the last line that runs.
; CHECK: .*error.*token: x!1.*
(assert (not x!1))
(check-sat)
