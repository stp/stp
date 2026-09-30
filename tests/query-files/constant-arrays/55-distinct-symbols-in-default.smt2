; RUN: %solver --array-equality --check-sanity %s | %OutputCheck %s
; RUN: %solver --array-equality --check-sanity --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --check-sanity --incremental=off %s | %OutputCheck %s
; A top-level DISTINCT cannot order symbols that also occur in a hidden
; default: x > y is satisfiable, but the proposed x < y < z chain is not.
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (distinct x y z))
(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8)))
               (ite (bvugt x y) #x01 #x02))))
(assert (= (select a #x00) #x01))
; CHECK: ^sat$
(check-sat)
; CHECK: true
(get-value ((bvugt x y)))
(push 1)
(assert (= x #x02))
(assert (= y #x01))
(assert (= z #x00))
; CHECK: ^sat$
(check-sat)
; CHECK: #x01
(get-value ((select a #xff)))
(assert (= x y))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
