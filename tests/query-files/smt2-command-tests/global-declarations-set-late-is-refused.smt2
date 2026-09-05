; Once a declaration exists, the option can no longer be set: pop reads the
; flag as it stands at the pop, so a late change would decide the scope of
; declarations already made. Refused rather than answered retroactively, and
; STP's :error-behavior is immediate-exit, so the query below never runs.
; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
; CHECK: ^\(error ".*:global-declarations must come before anything is declared or asserted"\)$
(set-option :global-declarations true)
(assert (= x #x1))
; CHECK-NOT: ^sat$
(check-sat)
