; RUN: %solver -d --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK: define-fun \|p\| \(\) \(Array \(_ BitVec 3\) \(_ BitVec 4\)\).*as const
; CHECK: define-fun \|q\| \(\) \(Array \(_ BitVec 3\) \(_ BitVec 4\)\).*as const
; Lowering discards the conjunct for a write that a later write to the
; same index shadows, and an equality nested in the discarded write's
; value goes with it. Its abstraction variable then enters no
; constraint, so the solver never assigns it.
;
; Two things have to hold once it is gone. The query still answers, so
; the counterexample check must not trip over an equality it can no
; longer resolve through a lowering -- it decides that one from the
; published cells instead. And (get-model) must be printable and
; consistent: p and q are unconstrained here, so both print as the
; all-zero array, which is the same array, which is what the discarded
; equality is worth in this model. Asserted by shape rather than by the
; exact printed text, because the printer's punctuation is not what this
; file is about.
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-fun a () (Array (_ BitVec 3) (_ BitVec 4)))
(declare-fun p () (Array (_ BitVec 3) (_ BitVec 4)))
(declare-fun q () (Array (_ BitVec 3) (_ BitVec 4)))
(declare-fun i () (_ BitVec 3))
(declare-fun j () (_ BitVec 3))
(declare-fun v () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (= (store (store (store a i (ite (= p q) #x1 #x0)) j y) i v) a))
(check-sat)
(get-model)
