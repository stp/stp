; RUN: %solver --SMTLIB2 %s | %OutputCheck --check-prefix=CONTROL %s
; RUN: not %solver --SMTLIB2 --lra-extension-mode=1 --lra-incremental-session=1 %s 2>&1 | %OutputCheck %s
;
; The contradictory query is unsat. Combining batch extension controls with
; an incremental Real session makes the coordinator throw before solving,
; and the batch driver returns SOLVER_ERROR. The printer must report that
; error and fail the process instead of falling through to its sat branch.
;
; CONTROL: ^unsat$
; CHECK-NOT: ^(sat|unsat|unknown)$
; CHECK: ^\(error "solver returned SOLVER_ERROR"\)$
; CHECK: ^Fatal Error: solver returned SOLVER_ERROR$
(set-logic QF_LRA)
(declare-const x Real)
(assert (> x 1))
(assert (< x 0))
(check-sat)
(exit)
