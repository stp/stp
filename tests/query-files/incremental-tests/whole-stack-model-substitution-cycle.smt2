; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on -d %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=off -d %s | %OutputCheck %s
;
; A per-level definition e1 -> ite(p0, 1, e0) and a later whole-stack
; elimination e0 -> e1 must not be replayed together. With p0 false their
; cycle used to grow the model evaluator's stack indefinitely (#1190).
(set-logic QF_ABVFP)
(declare-fun i1 () (_ FloatingPoint 3 2))
(declare-fun e0 () (_ BitVec 2))
(declare-fun e1 () (_ BitVec 2))
(declare-fun p0 () Bool)
; CHECK: ^sat$
(check-sat)
(assert (and (= (fp #b0 #b111 #b1) i1) (= e1 (ite p0 #b01 e0))))
; CHECK: ^sat$
(check-sat)
(push 1)
(assert (not p0))
; CHECK: ^sat$
(check-sat)
(assert (distinct ((as const (Array (_ FloatingPoint 3 2) (_ BitVec 2))) #b10) (store ((as const (Array (_ FloatingPoint 3 2) (_ BitVec 2))) #b00) (fp #b1 #b011 #b1) #b11)))
; CHECK: ^sat$
(check-sat)
