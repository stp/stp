; RUN: %solver --incremental=on %s | %OutputCheck %s
; RUN: %solver --incremental=on -d %s | %OutputCheck %s
;
; The application of g keeps every check of this session on the whole-stack
; route, and on that route a satisfiable UF round defers its public model to
; the first get-value or get-model, which rebuilds it from the SAT
; assignment. Each check below also needs the lazy array-equality checker
; (a float index or element, or a constant array, rules out the eager
; pointwise instantiation), and that checker owns every array read: the
; assignment holds no array cell, only the observations the checker
; certified, which the solve had published into the model the rebuild
; starts by clearing. The rebuilt model answered every read of an owned
; array with the default, so all three reads below came back #x00, +0.0
; and #x05 although the stack fixes them. -d builds the model during the
; solve and never rebuilt it.
(set-logic QF_AUFBVFP)
(set-option :produce-models true)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun b () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun p () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun q () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun r () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun x () (_ BitVec 8))
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(define-fun c () (_ FloatingPoint 8 24) (fp #b0 #b01111111 #b00000000000000000000000))
(assert (= (g x) #x01))

; A float index, under assumptions.
; CHECK: ^sat$
(check-sat-assuming ((= a b) (= (select b c) #x07)))
; CHECK: ^\( \(select \|a\| \(fp #b0 #b01111111 #b00000000000000000000000\)\) +#x07 \)$
; CHECK: ^\( \(select \|b\| \(fp #b0 #b01111111 #b00000000000000000000000\)\) +#x07 \)$
(get-value ((select a c) (select b c)))
; CHECK: define-fun \|a\| .*\(fp #b0 #b01111111 #b00000000000000000000000\) #x07\)
; CHECK: define-fun \|b\| .*\(fp #b0 #b01111111 #b00000000000000000000000\) #x07\)
(get-model)

; A float element, through a store, under push and pop.
(push 1)
(assert (= p (store q #x3 (fp #b0 #b10000000 #b00000000000000000000000))))
; CHECK: ^sat$
(check-sat)
; CHECK: ^\( \(select \|p\| +#x3\) +\(fp #b0 #b10000000 #b00000000000000000000000\) \)$
(get-value ((select p #x3)))
(pop 1)

; No float at all: a constant array keeps a bit-vector equality lazy too.
; CHECK: ^sat$
(check-sat-assuming ((= r (store ((as const (Array (_ BitVec 4) (_ BitVec 8))) #x05) i #x07)) (= i #x3)))
; CHECK: ^\( \(select \|r\| +#x3\) +#x07 \)$
(get-value ((select r #x3)))
