; The option takes a <b_value>, so a value that is neither true nor false is
; a malformed command rather than an unsupported one: it gets an error
; response, not "unsupported", and STP's :error-behavior is immediate-exit so
; nothing after it runs. The same holds for every option whose argument is a
; <b_value>; set-option-bad-boolean-value covers another of them.
; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error ".*:global-declarations takes true or false.*maybe"\)$
(set-option :global-declarations maybe)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
; CHECK-NOT: ^sat$
(check-sat)
