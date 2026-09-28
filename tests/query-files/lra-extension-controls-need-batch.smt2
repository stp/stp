; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The extension controls vary the batch solve's arithmetic state, and the
; Real session keeps that state across check-sats, so the two cannot be
; combined. The coordinator refuses the pair, but only once a Real query
; reaches it, so every Real query then failed with SOLVER_ERROR. The command
; line refuses it before reading the input instead.
; RUN: not %solver --SMTLIB2 --lra-persistent-state=1 --lra-extension-mode=2 %s 2>&1 | %OutputCheck --check-prefix=MODE %s
; RUN: not %solver --SMTLIB2 --lra-incremental-session=1 --lra-row-order=1 %s 2>&1 | %OutputCheck --check-prefix=ORDER %s
; RUN: not %solver --SMTLIB2 --lra-persistent-state=1 --lra-extension-restart-float-basis=1 %s 2>&1 | %OutputCheck --check-prefix=BASIS %s
; RUN: not %solver --SMTLIB2 --lra-incremental-session=1 --lra-extension-restart-sat=1 %s 2>&1 | %OutputCheck --check-prefix=SAT %s
; RUN: not %solver --SMTLIB2 --lra-extension-mode=3 --lra-row-order=2 --lra-incremental-session=1 --lra-persistent-state=1 %s 2>&1 | %OutputCheck --check-prefix=ALL %s
;
; The refusal is by value: 0 is each control's batch default, and a session
; option at 0 is no session.
; RUN: %solver --SMTLIB2 --lra-persistent-state=1 --lra-incremental-session=1 --lra-extension-mode=0 --lra-row-order=0 --lra-extension-restart-float-basis=0 --lra-extension-restart-sat=0 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --lra-persistent-state=0 --lra-incremental-session=0 --lra-extension-mode=2 --lra-row-order=1 --lra-extension-restart-float-basis=1 %s | %OutputCheck %s
;
; CHECK: ^unsat$
; MODE: ^ERROR: --lra-extension-mode=2 cannot be combined with --lra-persistent-state=1: the LRA extension controls apply to batch solves only$
; MODE-NOT: ^(sat|unsat|unknown)$
; ORDER: ^ERROR: --lra-row-order=1 cannot be combined with --lra-incremental-session=1: the LRA extension controls apply to batch solves only$
; ORDER-NOT: ^(sat|unsat|unknown)$
; BASIS: ^ERROR: --lra-extension-restart-float-basis=1 cannot be combined with --lra-persistent-state=1: the LRA extension controls apply to batch solves only$
; BASIS-NOT: ^(sat|unsat|unknown)$
; SAT: ^ERROR: --lra-extension-restart-sat=1 cannot be combined with --lra-incremental-session=1: the LRA extension controls apply to batch solves only$
; SAT-NOT: ^(sat|unsat|unknown)$
; ALL: ^ERROR: --lra-extension-mode=3, --lra-row-order=2 cannot be combined with --lra-incremental-session=1, --lra-persistent-state=1: the LRA extension controls apply to batch solves only$
; ALL-NOT: ^(sat|unsat|unknown)$
(set-logic QF_LRA)
(declare-const x Real)
(assert (> x 1))
(assert (< x 0))
(check-sat)
(exit)
