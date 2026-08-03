; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; CHECK-L: ( define-fun |i| () (_ BitVec 8) #x01 )
; CHECK-L: ( define-fun |b| () (Array (_ BitVec 4) (_ BitVec 8)) ((as const (Array (_ BitVec 4) (_ BitVec 8))) #x00 ) )
; i occurs once, so unconstrained-variable elimination replaces the
; disequality by a fresh boolean and defines i from select(b,j); the
; read then reaches the bit-blaster nowhere, and evaluating i against
; the model invents a value for b[j] on the spot. With array equality
; enabled the model printer emits a *total* interpretation for every
; array, filling in zero wherever it finds no concrete-index entry --
; so an invented value other than zero makes the printed b say
; b[0] = #x00 while i was computed from something else, and the model
; contradicts the assertion it was produced for.
;
; Pinned exactly because both halves must agree: b[0] is the value the
; evaluation used, and i is one more than it. The don't-care is zero
; precisely so that it agrees with the completion every other reader of
; the model applies -- the printer here, ReadUsingModel, and the
; contents comparison the post-solve audit makes -- without anything
; having to be recorded to keep them in step.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 4))
(assert (not (= a c)))
(assert (not (= i (select b j))))
(check-sat)
(get-model)
