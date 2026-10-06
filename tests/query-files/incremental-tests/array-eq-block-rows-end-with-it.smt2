; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at=1 --fp-abstraction=true --fp-abstraction-incremental=true %s | %OutputCheck %s
;
; The application of g sends every check of this session down the whole-
; stack route, each as one assumption-scoped block. The first block holds
; an array equality, so the array-equality transform abstracts its reads --
; of a, and of the write chain over a -- by variables of its own, and its
; assumptions keep the two cells apart, which forces i off +oo. The second
; block reads no array, so its transform never runs, and it used to skip
; recording its read rows as well. The first block's rows then stood in
; for the second's when get-model materialised the deferred model, their
; variables unconstrained since the first block was retracted. With i =
; +oo the row of (select (store a +oo (select a c)) i) folds onto the cell
; a[c], which the row of (select a c) holds with another value: get-model
; died with "conflicting model values for one concrete array index".
(set-logic QF_AUFBVFP)
(set-option :produce-models true)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun b () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun i () (_ FloatingPoint 8 24))
(declare-fun x () (_ BitVec 8))
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(define-fun c () (_ FloatingPoint 8 24) (fp #b0 #b01111111 #b00000000000000000000000))
(assert (= (g x) #x01))
; CHECK: ^sat$
(check-sat-assuming ((= a b) (bvult (select (store a (_ +oo 8 24) (select a c)) i) #x10) (bvugt (select a c) #x70)))
; CHECK: ^sat$
(check-sat-assuming ((= i (_ +oo 8 24))))
; CHECK: define-fun \|i\| .*\(fp #b0 #b11111111 #b00000000000000000000000\)
(get-model)
