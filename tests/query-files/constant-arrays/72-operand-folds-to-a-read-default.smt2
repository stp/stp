; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality -d %s | %OutputCheck %s
; As 70, with a default that is a read of another array: the folded anchor
; reads "name = (select a i)". The recovery took any read equated with a
; witness name for the witness read, found its index was i and not the
; witness index, and reported the index rewritten away, although the
; witness read had folded and i is the default's own index.
(set-logic QF_ABV)
(declare-fun y () (_ BitVec 4))
(declare-fun i () (_ BitVec 4))
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(assert (= (bvand y #x1) #x1))
(assert (= (ite (= ((_ extract 0 0) y) #b1)
                ((as const (Array (_ BitVec 4) (_ BitVec 4))) (select a i))
                a)
           ((as const (Array (_ BitVec 4) (_ BitVec 4))) y)))
; CHECK: ^sat$
(check-sat)
(assert (not (= (select a i) y)))
; CHECK: ^unsat$
(check-sat)
