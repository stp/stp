; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |a| () (_ BitVec 32) #x00000064)
; Replaces the sample-cvc a12/a13/a15/a103/a105/a107/a114-a116/a121-a126
; group, which declared a few symbols, asserted at most one equality or
; disequality over independent variables, and checked only that the answer
; was Invalid.  Those all held whatever the solver did with the constraints,
; so this keeps the shapes they covered -- an array declaration nobody reads,
; a symbol nothing mentions, an equality and a disequality on independent
; symbols -- and pins the one value a model has no freedom over.
(set-logic QF_ABV)
(set-option :produce-models true)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun mem () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun i () (_ BitVec 32))
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (= a #x00000064))
(assert (not (= b #x00000064)))
(check-sat)
(get-model)
