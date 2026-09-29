; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; (set-option :produce-models true) arms the counterexample check, which
; re-evaluates the submitted query and then compares every abstraction
; variable against the array cells the model publishes. Only the second
; half can see an equality go wrong: the first resolves each opaque
; equality through its own recorded lowering, which is the value the
; verdict already rested on.
;
; Both polarities appear here, because the two failure directions are
; caught by different branches. (= a b) is forced true, so its operands
; must carry identical certified contents at every cell -- and the two
; reads sit at distinct constant indices, one under each operand, so
; neither direction of propagation across the equality can be dropped
; without a cell going missing on one side. Constants rather than
; variables on purpose: a symbolic index is free to coincide with the
; witness index, and then a one-directional propagation still produces
; agreeing contents by luck.
;
; (distinct a c) is forced false, so its operands must genuinely differ
; somewhere in the published model -- which is what the witness index of
; preprocessing step 1 supplies.
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-fun a () (Array (_ BitVec 3) (_ BitVec 4)))
(declare-fun b () (Array (_ BitVec 3) (_ BitVec 4)))
(declare-fun c () (Array (_ BitVec 3) (_ BitVec 4)))
(assert (= a b))
(assert (distinct a c))
(assert (= (select a #b001) #x7))
(assert (= (select b #b010) #x3))
(assert (= (select c #b001) #x5))
(check-sat)
