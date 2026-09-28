; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A read at a term's index names an element of S, so rule K's refutation
; stands whatever size a model gives the sort.
(set-logic QF_AUFBV)
(declare-sort S 0)
(declare-fun u () S)
(declare-fun a () (Array S (_ BitVec 1)))
(assert (= a ((as const (Array S (_ BitVec 1))) #b0)))
(assert (= (select a u) #b1))
(check-sat)
