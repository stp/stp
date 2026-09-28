; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; CHECK-L: (define-fun |i| () (_ BitVec 8) #x01)
; CHECK-L: (define-fun |b| () (Array (_ BitVec 4) (_ BitVec 8)) (store ((as const (Array (_ BitVec 4) (_ BitVec 8))) #x00) #x0 #x00))
; Unconstrained-variable elimination reaches this disequality from
; either side: i occurs once, and so does the array b beneath the read.
; The read rule is the one that fires -- select(b,j) with b free is
; itself free -- so the read becomes a fresh value and b is defined as a
; write of it, which is why b prints with an explicit cell rather than
; as the bare constant array. (Before the array rules existed it was i
; that was eliminated, defined from select(b,j), and b printed with no
; cells at all.)
;
; Either way the model has to be self-consistent, which is what this
; pins: b[0] is the value the evaluation used, and i is one more than
; it. With array equality enabled the model printer emits a *total*
; interpretation for every array, filling in zero wherever it finds no
; concrete-index entry, so a b whose printed cells disagreed with the
; value i was computed from would contradict the assertion the model was
; produced for. The don't-care is zero precisely so that it agrees with
; the completion every other reader of the model applies -- the printer
; here, ReadUsingModel, and the contents comparison the post-solve audit
; makes -- without anything having to be recorded to keep them in step.
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 4))
(assert (not (= a c)))
(assert (not (= i (select b j))))
(check-sat)
(get-model)
