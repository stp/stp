; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=off %s | %OutputCheck %s
; Each default hides a read over another constant array. FP preparation must
; visit the nested defaults with its worklist rather than recurse through them.
(set-option :produce-models true)
(set-logic QF_ABVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(declare-fun a () (Array (_ BitVec 8) (_ FloatingPoint 8 24)))
(define-fun a0 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) x))
(define-fun a1 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a0 i y) j)))
(define-fun a2 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a1 i y) j)))
(define-fun a3 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a2 i y) j)))
(define-fun a4 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a3 i y) j)))
(define-fun a5 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a4 i y) j)))
(define-fun a6 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a5 i y) j)))
(define-fun a7 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a6 i y) j)))
(define-fun a8 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a7 i y) j)))
(define-fun a9 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a8 i y) j)))
(define-fun a10 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a9 i y) j)))
(define-fun a11 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a10 i y) j)))
(define-fun a12 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a11 i y) j)))
(define-fun a13 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a12 i y) j)))
(define-fun a14 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a13 i y) j)))
(define-fun a15 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a14 i y) j)))
(define-fun a16 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a15 i y) j)))
(define-fun a17 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a16 i y) j)))
(define-fun a18 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a17 i y) j)))
(define-fun a19 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)) ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24))) (select (store a18 i y) j)))
(assert (= a a19))
; CHECK: ^sat$
(check-sat)
(push 1)
(assert (= i j))
(assert (= y ((_ to_fp 8 24) #x40400000)))
; CHECK: ^sat$
(check-sat)
; CHECK: #x40400000
(get-value ((fp.to_ieee_bv (select a #x09))))
(assert (not (fp.eq (select a #x09) ((_ to_fp 8 24) #x40400000))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
