; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
; A sort a cover bounds has the elements its terms name and no others, so
; every value of it is one of them: a symbol the solve never valued, a
; function's value where the model has no case for it, a read. The model
; says so, in a comment, since its definitions alone do not. And no pass
; may assume a variable of the sort can be made to differ from a term,
; which needs a second element: unconstrained elimination once turned the
; third query's disequality into a free Boolean and answered sat.
(set-option :produce-models true)
(set-logic QF_AUFBV)
(declare-sort S 0)
(declare-fun s1 () S)
(declare-fun s2 () S)
(declare-fun s9 () S)
(declare-fun f (S) S)
(declare-fun b () (Array S S))
(push 1)
(assert (= (store (store ((as const (Array S (_ BitVec 8))) #x00) s1 #x01) s2 #x01)
           ((as const (Array S (_ BitVec 8))) #x01)))
(assert (or (= s9 s9) (= (f s9) s1)))
; CHECK: ^sat$
(check-sat)
; CHECK-NEXT: ^\($
; CHECK-NEXT: true
; CHECK-NEXT: true
; CHECK-NEXT: true
(get-value ((or (= s9 s1) (= s9 s2))
            (or (= (f s2) s1) (= (f s2) s2))
            (= (store (store ((as const (Array S (_ BitVec 8))) #x00) s1 #x01) s2 #x01)
               ((as const (Array S (_ BitVec 8))) #x01))))
; CHECK: ^; S has exactly these elements: \(forall \(\(x S\)\) 
(get-model)
(pop 1)
; A function's values count: three distinct elements.
(push 1)
(assert (= (store (store ((as const (Array S (_ BitVec 8))) #x00) s1 #x01) s2 #x01)
           ((as const (Array S (_ BitVec 8))) #x01)))
(assert (distinct s1 s2 (f s1)))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; S is just s1, so a read of an array of S is s1.
(push 1)
(assert (= (store ((as const (Array S (_ BitVec 8))) #x00) s1 #x01)
           ((as const (Array S (_ BitVec 8))) #x01)))
(assert (not (= (select b s1) s1)))
; CHECK: ^unsat$
(check-sat)
(pop 1)
