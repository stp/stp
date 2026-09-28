; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^unsat
; The second S is another sort than the popped one, spelled alike. Constant
; arrays were interned by their sort's text, so the second frame's constant
; array was the first's, of the popped sort, and the script was refused.
(set-logic QF_AUFBV)
(push 1)
(declare-sort S 0)
(declare-fun a () (Array S (_ BitVec 4)))
(declare-fun i () S)
(assert (= a ((as const (Array S (_ BitVec 4))) #x1)))
(assert (= (select a i) #x1))
(check-sat)
(pop 1)
(declare-sort S 0)
(declare-fun b () (Array S (_ BitVec 4)))
(declare-fun j () S)
(assert (= b ((as const (Array S (_ BitVec 4))) #x1)))
(assert (= (select b j) #x2))
(check-sat)
(push 1)
(assert (= (select b j) #x1))
(check-sat)
(pop 1)
