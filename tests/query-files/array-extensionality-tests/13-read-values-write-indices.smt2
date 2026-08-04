; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Read values used as write indices and write values (Example 7 of the
; paper) exercise scalar naming and write-access semantics.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun c () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i1 () (_ BitVec 2))
(declare-fun i2 () (_ BitVec 2))
(declare-fun k () (_ BitVec 2))
(declare-fun e () (_ BitVec 2))
(assert (= (store b (select a i1) (select a i2)) (store c k e)))
(assert (= (select a i1) k))
(assert (distinct (select a i2) e))
(check-sat)
