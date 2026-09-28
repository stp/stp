; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK-L: STP cannot decide equality between whole array terms without --array-equality
; RUN: %solver --array-equality %s | %OutputCheck --check-prefix=WITHFLAG %s
; WITHFLAG: ^unsat
; a = b and a[i] != b[i] is unsatisfiable, and cvc5 1.0.1 agrees.
;
; Without --array-equality STP used to warn and then answer SAT. The
; warning was the only thing between a caller and a wrong verdict:
; nothing eliminates the array-sorted operands of the equality, so the
; transform leaves them and the solve proceeds as though the atom were
; unconstrained. A debug build aborted instead, on
;   Assertion `!containsArrayOps(inputToSat, bm)'
; which claims ackermannisation removed every array operation -- untrue
; precisely when an array equality is present. Reproduces on upstream
; master, so it long predates this feature; the feature is what makes
; refusing the right answer rather than a regression.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(assert (= a b))
(assert (distinct (select a i) (select b i)))
(check-sat)
