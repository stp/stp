; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; CHECK-L: ( define-fun |i| () (_ BitVec 8) #x00 )
; CHECK-L: ( define-fun |b| () (Array (_ BitVec 4) (_ BitVec 8)) (store ((as const (Array (_ BitVec 4) (_ BitVec 8))) #x00 ) #x0 #xFF ) )
; i occurs once, so unconstrained-variable elimination replaces the
; disequality by a fresh boolean and defines i from select(b,j); the
; read then reaches the bit-blaster nowhere, and evaluating i against
; the model invents a value for b[j] on the spot. With array equality
; enabled the model printer emits a *total* interpretation for every
; array, filling in zero wherever it finds no concrete-index entry --
; so unless the invented value is recorded under that key, the printed
; b says b[0] = #x00 while i was computed from b[0] = #xFF, and the
; model contradicts the assertion it was produced for.
;
; Pinned exactly because both halves must agree: b[0] is the value the
; evaluation used, and i is one more than it. The specific don't-care
; (#xFF, from CreateMaxConst) is not the point -- changing it must
; change both lines together.
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
