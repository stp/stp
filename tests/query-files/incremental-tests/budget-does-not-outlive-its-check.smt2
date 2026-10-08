; A budget is the check's it was set for. The incremental driver keeps one SAT
; backend for every check-sat and arms it again per check, but arming only ever
; set a budget, never cleared one: once a budget had been unset, the next check
; still stopped where the one before it did, and both legs here answered
; unknown twice under --incremental=on. The batch pipeline builds a backend per
; check and is the control.
;
; Budgets of zero, as in reason-unknown-names-the-budget.smt2, so that the
; budgeted checks give up whatever the solver. The time leg pushes a new
; assertion so that it is a new query rather than a repeat of the answered one.
;
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-const x (_ BitVec 40))
(declare-const y (_ BitVec 40))
; 46337 * 46327, with both factors held below 2^16 so the product cannot wrap
(assert (= (bvmul x y) (_ bv2146654199 40)))
(assert (bvugt x (_ bv1 40)))
(assert (bvugt y (_ bv1 40)))
(assert (bvult x (_ bv65536 40)))
(assert (bvult y (_ bv65536 40)))

(set-option :max-num-confl 0)
; CHECK: ^unknown$
(check-sat)
; CHECK-NEXT: :reason-unknown \(incomplete "the conflict budget set by --max-num-confl ran out"\)
(get-info :reason-unknown)
(set-option :max-num-confl -1)
; CHECK-NEXT: ^sat$
(check-sat)

(push 1)
(assert (bvult x y))
(set-option :max-time 0)
; CHECK-NEXT: ^unknown$
(check-sat)
; CHECK-NEXT: :reason-unknown timeout
(get-info :reason-unknown)
(set-option :max-time -1)
; CHECK-NEXT: ^sat$
(check-sat)
(pop 1)
