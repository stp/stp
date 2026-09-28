; RUN: %solver --SMTLIB2 --lra-presolve-monotone=0 --lra-presolve-unconstrained 1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --lra-presolve-monotone=1 %s | %OutputCheck --check-prefix=SOLVED %s
;
; Building the LRA problem does exact arithmetic at four layers, and each one
; refuses in its own currency. The solve context already separates a budget it
; ran out of from a state that is wrong, but the coordinator rethrew both as a
; bare runtime_error carrying only the message, so the top of the solver saw
; one untyped thing and answered SOLVER_ERROR: this interface's "the call was
; malformed", the one verdict that carries no reason. The query below is well
; formed and merely too big for the core, so that was the wrong answer twice
; over -- and it left STP printing "unknown" and then denying it had, because
; the reason API had nothing recorded to report.
;
; Reduced by delta debugging from a murxla trace. The verdict alone does not
; witness the fix: the SMT-LIB printer already mapped SOLVER_ERROR to unknown,
; so it is the reason that has to be asked for. Through the C interface the
; same answer used to arrive as a raw -100, on a boundary documented to answer
; 0, 1, 2 or 3.
; CHECK-NEXT: ^unknown$
; CHECK-NEXT-L: (:reason-unknown (incomplete "the exact linear arithmetic solver could not decide this query within its resource budget: exact assertion reached a resource limit"))
; Monotone elimination avoids the large core row and reconstructs a checked model.
; SOLVED: ^sat$
; SOLVED-NEXT-L: (:reason-unknown (error "the last answer was not unknown"))
(set-logic QF_LRA)
(declare-const _x0 Real)
(declare-const _x1 Real)
(assert (let ((_let0 (* (/ 2398621974 52) 8399211566062017098976597677352.0 (/ 2398621974 52) 8399211566062017098976597677352.0 8399211566062017098976597677352.0)))(let ((_let1 (+ _let0 _let0 _let0)))(let ((_let2 (* _let1 _let0)))(let ((_let3 (* _let2 _let0 (/ 2398621974 52) (/ 2398621974 52))))(let ((_let4 (* _let3 _let2 _let1)))(let ((_let5 (* _let4 _let1)))(let ((_let6 (* _let3 _let5 _let5 _let4 (/ 2398621974 52))))(let ((_let7 (- _let6)))(let ((_let8 (- _let7 _x1)))(let ((_let9 (+ (* _let8 _let4 _let7 _let6) _let6 _let7 _x1)))(let ((_let10 (- _let9)))(let ((_let11 (* _let10 _let3)))(let ((_let12 (+ (+ (+ _x0 _let8) _let10) _let7)))(>= (+ _let9 (+ (- (- _let12 (* _let11 _let6 (/ 2398621974 52))) (- _let12)) (+ _let9 _let11 _x0 _x1 _let7))) _x0)))))))))))))))
(check-sat)
(get-info :reason-unknown)
(exit)
