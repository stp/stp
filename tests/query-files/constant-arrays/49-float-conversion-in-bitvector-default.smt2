; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=off %s | %OutputCheck %s
; Detect FP syntax inside a BV array's default before deciding whether to run
; FP preparation. No FP operation is visible outside the first hidden default.
(set-option :produce-models true)
(set-logic QF_ABVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8)))
             ((_ fp.to_ubv 8) RNE x))))
; CHECK: ^sat$
(check-sat)
(push 1)
(assert (= x ((_ to_fp 8 24) #x40200000)))
; CHECK: ^sat$
(check-sat)
; CHECK: #x02
(get-value ((select a #x09)))
(assert (distinct (select a #x09) #x02))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
