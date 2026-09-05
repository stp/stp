; Model production is a property of the current query, not of a previous
; solve's derived construct_counterexample_flag.  This must therefore work
; when the first persistent solve takes the whole-array-equality route.
; RUN: %solver --array-equality --incremental %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental-auto-engage-at 1 %s | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun x () (_ BitVec 2))

; A pushed first query exercises both explicit and automatically engaged
; incremental sessions without an ordinary query first priming model state.
(push 1)
(assert (= a b))
(assert (= (select a #b00) #b10))
(assert (= x (select b #b00)))
; CHECK: ^sat
(check-sat)
; CHECK: \|x\| +#b10
(get-value (x))
(pop 1)
(exit)
