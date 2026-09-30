; RUN: %solver --array-equality --check-sanity %s | %OutputCheck %s
; RUN: %solver --array-equality --check-sanity --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --check-sanity --incremental=off %s | %OutputCheck %s
; Reads in defaults lead to further constant arrays. Lowering must reach
; the DISTINCT in the innermost default, even through both store misses.
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(define-fun inner () (Array (_ BitVec 8) (_ BitVec 8))
  ((as const (Array (_ BitVec 8) (_ BitVec 8)))
    (ite (distinct x y z) #x01 #x02)))
(define-fun middle () (Array (_ BitVec 8) (_ BitVec 8))
  ((as const (Array (_ BitVec 8) (_ BitVec 8)))
    (select (store inner i #xff) j)))
(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8)))
               (select (store middle i #xfe) j))))
(assert (distinct i j))
(assert (= x y))
; CHECK: ^sat$
(check-sat)
; CHECK: #x02
(get-value ((select a #x00)))
(push 1)
(assert (= (select a #x00) #x01))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
