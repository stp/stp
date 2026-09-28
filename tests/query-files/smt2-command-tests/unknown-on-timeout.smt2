; A solve that runs out of budget answers `unknown`, and says which budget.
;
; The no-answer channel printed "Timed Out." in every mode, including SMT-LIB,
; where a caller cannot act on a sentence and where there is a word for this.
; So `unknown` is what SMT-LIB mode prints, and (get-info :reason-unknown)
; carries the reason.
;
; Two budgets share that exit and they are not the same claim. The wall clock
; (-k) may succeed with more time on the same machine; the conflict budget (-g,
; --max-num-confl) is deterministic and will not, so reporting `timeout` for it
; is a false statement of the one thing a caller would act on. The first
; version of this fixture ran -g and pinned `timeout`, in a run that finished
; in a tenth of a second.
;
; The CVC rendering is pinned in unknown-on-budget.cvc rather than here: that
; language has no reason command, so it reports the generic verdict as
; `Unknown.`. The parser is chosen by file extension, so a .smt2 file cannot
; exercise that path.
;
; The clock leg asks for zero seconds. That is deterministic -- the budget is
; spent before the solver is entered, which is the case the pre-check exists
; for -- where a one-second budget on a hard query is a race that a fast
; machine wins and a slow one loses. Ten 32-bit multiplies with a distinct over
; the operands.
;
; RUN: %solver -g 2 %s 2>&1 | %OutputCheck --check-prefix=CONFL %s
; RUN: %solver -k 0 %s 2>&1 | %OutputCheck --check-prefix=CLOCK %s
; RUN: %solver -k 0 -g 2 %s 2>&1 | %OutputCheck --check-prefix=CLOCK %s
;
; CONFL: ^unknown$
; CONFL: :reason-unknown \(incomplete "the conflict budget set by --max-num-confl ran out"\)
; CONFL-NOT: reason-unknown timeout
;
; The third run sets both budgets and the clock has already gone, so the clock
; is the answer: asking the solver which of its own limits expired is the only
; way to tell a zero-second limit from no limit at all.
; CLOCK: ^unknown$
; CLOCK: :reason-unknown timeout
;
(set-logic QF_BV)
(declare-fun x0 () (_ BitVec 32))
(declare-fun x1 () (_ BitVec 32))
(declare-fun x2 () (_ BitVec 32))
(declare-fun x3 () (_ BitVec 32))
(declare-fun x4 () (_ BitVec 32))
(declare-fun x5 () (_ BitVec 32))
(declare-fun x6 () (_ BitVec 32))
(declare-fun x7 () (_ BitVec 32))
(declare-fun x8 () (_ BitVec 32))
(declare-fun x9 () (_ BitVec 32))
(declare-fun mk () (_ BitVec 32))
(assert (= (bvmul (bvmul (bvmul x0 x1) (bvmul x2 x3)) (bvmul (bvmul x4 x5) (bvmul x6 x7))) (bvmul x8 x9)))
(assert (= (bvmul x8 x9) mk))
(assert (bvugt mk #x7ffffff0))
(assert (bvugt x0 #x00000001))
(assert (bvugt x1 #x00000001))
(assert (distinct x0 x1 x2 x3 x4 x5 x6 x7 x8 x9))
(check-sat)
(get-info :reason-unknown)
