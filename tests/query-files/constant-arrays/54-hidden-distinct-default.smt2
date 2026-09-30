; RUN: %solver --array-equality --check-sanity %s | %OutputCheck %s
; RUN: %solver --array-equality --check-sanity --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --check-sanity --incremental=off %s | %OutputCheck %s
; DISTINCT occurs only in the constant-array default and must be lowered
; before bit-blasting. Equal operands force every cell to #x02.
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8)))
               (ite (distinct x y z) #x01 #x02))))
(assert (= x y))
(push 1)
(assert (distinct (select a #x00) #x02))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
; CHECK: #x02
(get-value ((select a #x00)))
