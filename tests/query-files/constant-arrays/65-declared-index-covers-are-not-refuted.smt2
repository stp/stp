; RUN: %solver %s | %OutputCheck %s
; RUN: %solver -d %s | %OutputCheck %s
; A declared sort may have as few elements as its terms name. A store chain
; over a constant array equated with another constant array can say every
; element is one of the stored-at terms, so such a cover bounds the sort
; from above, and a solver that treats the sort as unbounded refutes a
; satisfiable formula: the first, second and fourth below.
(set-logic QF_AUFBV)
(declare-sort S 0)
(declare-fun s1 () S)
(declare-fun s2 () S)
(declare-fun s3 () S)
; Every element is s1 or s2: S has at most two.
(push 1)
(assert (= (store (store ((as const (Array S (_ BitVec 8))) #x00) s1 #x01) s2 #x01)
           ((as const (Array S (_ BitVec 8))) #x01)))
; CHECK: ^sat$
(check-sat)
(pop 1)
; S has exactly the one element s1.
(push 1)
(assert (= (store ((as const (Array S (_ BitVec 8))) #x00) s1 #x01)
           ((as const (Array S (_ BitVec 8))) #x01)))
; CHECK: ^sat$
(check-sat)
(pop 1)
; At most two elements, three distinct ones.
(push 1)
(assert (= (store (store ((as const (Array S (_ BitVec 8))) #x00) s1 #x01) s2 #x01)
           ((as const (Array S (_ BitVec 8))) #x01)))
(assert (distinct s1 s2 s3))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; Two chains over different constant arrays, at the same two indexes: one
; array when S is just those two and the stored values agree pairwise.
(push 1)
(declare-fun v1 () (_ BitVec 8))
(declare-fun v2 () (_ BitVec 8))
(declare-fun w1 () (_ BitVec 8))
(declare-fun w2 () (_ BitVec 8))
(assert (= (store (store ((as const (Array S (_ BitVec 8))) #x00) s1 v1) s2 v2)
           (store (store ((as const (Array S (_ BitVec 8))) #x01) s1 w1) s2 w2)))
; CHECK: ^sat$
(check-sat)
(pop 1)
