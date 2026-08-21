; Both drivers name the budget that stopped them, and name the same one.
;
; A no-answer leaves either driver as SOLVER_TIMEOUT, which is the same value
; whichever budget ran out, so which one it was has to be taken from the SAT
; solver while it is still there to be asked. The batch pipeline did that in
; ToSATAIG::runSolver and the incremental driver did not, so the same query
; stopped by the same flag was named through one and denied through the other:
; --incremental=on answered a bare `unknown` to every (get-info
; :reason-unknown), whichever budget it had been given.
;
; The distinction is the one a caller acts on, which is why it is worth
; carrying: the clock may succeed with more time on the same machine, while
; the conflict budget is deterministic and re-running with a year will
; reproduce it exactly. What is worth doing there is raising --max-num-confl.
;
; Four legs: two budgets across two drivers, so that the answer is pinned to
; the budget and not to the way the query was solved. Both budgets are set to
; zero rather than to something small, so that no leg depends on a solver
; being unlucky enough to need one more conflict or one more millisecond: a
; deadline of now has already passed, and a query that needs any search at all
; exceeds a budget of no conflicts. The query is a real factorisation --
; zero-extended so the product cannot wrap, since modular multiplication would
; make it trivially satisfiable and no budget would bind.
;
; A clock is asked about first and a conflict budget second, because
; timeLimitExpired() is what tells them apart and a zero-second limit is
; indistinguishable from no limit at the flags.
;
; RUN: %solver --incremental=off --max-time=0 %s 2>&1 | %OutputCheck --check-prefix=BATCHCLOCK %s
; RUN: %solver --incremental=on --max-time=0 %s 2>&1 | %OutputCheck --check-prefix=INCCLOCK %s
; RUN: %solver --incremental=off --max-num-confl=0 %s 2>&1 | %OutputCheck --check-prefix=BATCHCONFL %s
; RUN: %solver --incremental=on --max-num-confl=0 %s 2>&1 | %OutputCheck --check-prefix=INCCONFL %s
;
; BATCHCLOCK: ^unknown$
; BATCHCLOCK: ^\(:reason-unknown timeout\)$
;
; INCCLOCK: ^unknown$
; INCCLOCK: ^\(:reason-unknown timeout\)$
; INCCLOCK-NOT: reason-unknown unknown
;
; BATCHCONFL: ^unknown$
; BATCHCONFL: :reason-unknown \(incomplete "the conflict budget set by --max-num-confl ran out"\)
;
; INCCONFL: ^unknown$
; INCCONFL: :reason-unknown \(incomplete "the conflict budget set by --max-num-confl ran out"\)
; INCCONFL-NOT: reason-unknown unknown
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (= (bvmul ((_ zero_extend 32) a) ((_ zero_extend 32) b)) #x7ffffffc80000005))
(assert (bvugt a #x00000001))
(assert (bvugt b #x00000001))
(check-sat)
(get-info :reason-unknown)
