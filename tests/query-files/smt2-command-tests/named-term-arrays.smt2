; Labels on array terms, extensional equality, const arrays and distinct
; stand for their term exactly: get-value prints the same value for both.
; RUN: %solver %s | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 2) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 2) (_ BitVec 8)))
(assert (! (= a b) :named ext))
(assert (= (select (! (store a #b01 #xff) :named s) #b01) (! #xff :named ff)))
(assert (= (! a :named na) (! b :named nb)))
(assert (= (select a #b00) #x07))
(assert (! (distinct (store a #b00 #x00) a) :named da))
(declare-const c (Array (_ BitVec 2) (_ BitVec 8)))
(assert (= c (! ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x07) :named ca)))
; CHECK: ^sat$
(check-sat)
; CHECK-L: (ext true)
; CHECK-L: ((= a b) true)
; CHECK-L: (ff #xFF)
; CHECK-L: ((select s #b01) #xFF)
; CHECK-L: ((select (store a #b01 #xff) #b01) #xFF)
; CHECK-L: (na (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x00) #b00 #x07))
; CHECK-L: (a (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x00) #b00 #x07))
; CHECK-L: ((= na nb) true)
; CHECK-L: (da true)
; CHECK-L: ((distinct (store a #b00 #x00) a) true)
; CHECK-L: ((select ca #b11) #x07)
; CHECK-L: ((select c #b11) #x07)
(get-value (ext (= a b) ff (select s #b01) (select (store a #b01 #xff) #b01) na a (= na nb) da (distinct (store a #b00 #x00) a) (select ca #b11) (select c #b11)))
; CHECK-NOT: define-fun \|na\|
; CHECK-NOT: define-fun \|ca\|
; CHECK: define-fun \|c\|
(get-model)
