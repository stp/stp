; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: define-fun |a| () (Array (_ FloatingPoint 8 24) (_ BitVec 8))
; A store at a symbolic NaN index is hit by a select at a NaN literal
; of another payload, under a dissolved whole-array disequality; the
; candidate-model re-check used to compare the interned float literal
; index against plain evaluated bits by node identity, miss the write,
; and die on an "unreachable" refinement assertion.
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (= (select (store a x #x11) (fp #b0 #b11111111 #b00000000000000000000001)) #x11))
(assert (not (= a (store a x #x11))))
(check-sat)
(get-model)
