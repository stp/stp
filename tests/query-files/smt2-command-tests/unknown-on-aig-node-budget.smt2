; The AIG node budget is a third way to run out, and it has to name itself.
;
; --aig-node-budget stops bit-blasting before the AIG eats the machine, so the
; query gets no answer. That no-answer leaves through the same door a clock
; expiry does -- soft_timeout_expired, so the pipeline unwinds the one way it
; knows -- and the reason has to be recorded at the throw site, because by the
; time it surfaces the flag is all that is left and it says "clock".
;
; Before it was recorded, the budget answered `unknown` and then told a caller
; who asked why that the last answer was not unknown. Both halves were wrong:
; there was an unknown to explain, and the thing to explain was a budget.
;
; It is not a timeout, and the distinction is the one a caller acts on. The
; clock may succeed with more time on the same machine; this budget is
; deterministic and re-running with a year will reproduce it exactly. What is
; worth doing instead is raising the flag, so the message names the flag, the
; count it stopped at, and the value that lifts the limit altogether.
;
; The count is left loose here. It is deterministic for a given bit-blaster --
; three runs of this file give the same number -- but it is a fact about the
; encoding, not about the budget, and pinning it would make an unrelated
; improvement to bit-blasting look like a regression in the reporting.
;
; The batch path is what is pinned: --incremental=on solves through a
; different driver that the budget is not wired into, so a leg run there would
; pass by answering the query rather than by exhausting anything. This input
; pushes nothing, so the default --incremental=auto would stay batch anyway;
; saying so is what stops the leg from starting to measure something else if
; that default ever moves.
;
; The second leg is the control. -1 is the value that lifts the limit -- 0 is
; a budget of no gates at all, which gives up before the first one -- so the
; same query is answered there, which is what says the first leg exhausted a
; budget rather than merely found the query hard. The sentence the first leg
; prints is pinned including that -1, since a message that named the wrong
; sentinel would send a caller to the one value that reproduces their problem.
;
; RUN: %solver --incremental=off --aig-node-budget=100 %s 2>&1 | %OutputCheck --check-prefix=CAPPED %s
; RUN: %solver --incremental=off --aig-node-budget=-1 %s 2>&1 | %OutputCheck --check-prefix=UNCAPPED %s
;
; CAPPED: ^unknown$
; CAPPED: :reason-unknown \(incomplete "the AIG node budget set by --aig-node-budget \(100\) ran out at [0-9]+ AND gates; raise it, or set it to -1 for no limit"\)
; CAPPED-NOT: reason-unknown timeout
; CAPPED-NOT: the last answer was not unknown
;
; UNCAPPED: ^sat$
; UNCAPPED: :reason-unknown \(error "the last answer was not unknown"\)
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(assert (= (bvmul a b) #x0000000d1f2e3c4b))
(assert (bvugt a #x0000000000000001))
(assert (bvugt b #x0000000000000001))
(check-sat)
(get-info :reason-unknown)
