; RUN: %solver --incremental=on --ackermanize -d %s | %OutputCheck %s
; RUN: %solver --incremental=on -d %s | %OutputCheck %s
; RUN: %solver --incremental=off --ackermanize -d %s | %OutputCheck %s
;
; The -d self-check re-evaluates the raw assertion stack against the model,
; and under eager Ackermannisation the reads it meets were compiled away
; before encoding: the evaluator must answer them from the recorded
; observations, not from an invented completion. Three shapes an invented
; value would break: a read the stack asserts directly, a read-over-write
; whose fall-through lands on a base cell the stack never reads directly,
; and a cache-backed re-check whose observations must be restored rather
; than rebuilt. A wrong completion turns a genuine model into a self-check
; abort, so every answer below must arrive.
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(push 1)
(assert (= (select a i) #x05))
(check-sat)
(check-sat)
(push 1)
(assert (= (select (store a j #x09) i) #x05))
(assert (distinct i j))
(check-sat)
(push 1)
(assert (= (select a j) #x07))
(check-sat)
(exit)
