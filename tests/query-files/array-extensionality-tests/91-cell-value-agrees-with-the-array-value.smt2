; A value a model query reports cannot disagree with the model it was taken
; from. With the extension off, an unobserved cell used to complete to all-ones
; while the printer filled the same array with zero, so one reply said both:
;
;   ( |a| ((as const (Array (_ BitVec 4) (_ BitVec 6))) #b000000) )
;   ( (select |a| #x0)  #b111111 )
;
; Nothing constrains this array, so any total interpretation is a model -- but
; only one of them is the one being published. get-model, get-value of the
; array, and get-value of any cell all have to name the same one.
; RUN: %solver %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK: \(define-fun \|a\| \(\) \(Array \(_ BitVec 4\) \(_ BitVec 6\)\) \(\(as const \(Array \(_ BitVec 4\) \(_ BitVec 6\)\)\) #b000000\)\)
; CHECK: \(select a \(_ bv0 4\)\) #b000000
; CHECK: \(select a \(_ bv3 4\)\) #b000000
; CHECK-NOT: #b111111
(set-option :produce-models true)
(set-logic QF_ABV)
(set-option :array-equality off)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 6)))
(check-sat)
(get-model)
(get-value (a (select a (_ bv0 4)) (select a (_ bv3 4))))
(exit)
