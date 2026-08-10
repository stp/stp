; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The mirror image of the previous test: the contradiction lives in
; congruence across a = b, while unrelated array c carries satisfiable
; read constraints. Both components are owned by the active checker,
; and only an extensionality lemma can conclude unsat.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(declare-fun k () (_ BitVec 4))
(declare-fun l () (_ BitVec 4))
(assert (= a b))
(assert (= i j))
(assert (distinct (select a i) (select b j)))
(assert (= (select c k) #x07))
(assert (= (select c l) #x09))
(check-sat)
