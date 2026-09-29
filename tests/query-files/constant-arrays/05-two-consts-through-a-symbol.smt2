; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; One array equal to two constant arrays with different defaults: no cell can
; hold both, and nothing reads the array (checker rule K').
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x01)))
(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x02)))
(check-sat)
