; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The mirror image of the previous test: the contradiction lives in
; the equality cone (congruence across a = b), while the unrelated
; array c carries satisfiable read constraints that classic refinement
; handles. Reads of a and b are exempt from the classic read axioms,
; so only an equality lemma can conclude unsat with c's machinery
; interleaved in the same refinement loop.
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
