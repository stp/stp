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
; machine wins and a slow one loses.
;
; The conflict leg needs a query no backend answers inside two conflicts, and
; a satisfiable one cannot promise that: the ten multiplies with a distinct
; over the operands that used to stand here, CryptoMiniSat 5.16 solves within
; them. So the query is unsatisfiable instead, with nothing for a good first
; assignment to find and nothing a preprocessor can refute up front: two
; 32-bit factors, neither of them 1, of the largest prime below 2^62.
; Refuting that is factoring.
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
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvmul ((_ zero_extend 32) x) ((_ zero_extend 32) y)) #x3fffffffffffffc7))
(assert (bvugt x #x00000001))
(assert (bvugt y #x00000001))
(check-sat)
(get-info :reason-unknown)
