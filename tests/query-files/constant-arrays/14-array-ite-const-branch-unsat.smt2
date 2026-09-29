; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; An array equal to an if-then-else whose selected branch is a constant array.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun d () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () Bool)
(assert (= a (ite b ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x01) d)))
(assert b)
(assert (not (= (select a #x02) #x01)))
(check-sat)
