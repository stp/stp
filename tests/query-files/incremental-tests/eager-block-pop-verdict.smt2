; RUN: %solver --cadical --incremental-auto-engage-at=1 %s | %OutputCheck %s
; RUN: %solver --cadical --incremental-auto-engage-at=1 -d %s | %OutputCheck %s
; RUN: %solver --cadical --incremental-auto-engage-at=1 --ackermanize -d %s | %OutputCheck %s
; RUN: %solver --cadical --incremental=on -d %s | %OutputCheck %s
; RUN: %solver --cadical -d %s | %OutputCheck %s
;
; The base reads a[i] lazily, as a registry row that read refinement
; owns. The second check-sat takes the eager instantiation arm for its
; array equality, and that arm's --ackermanize used to outlive the block.
; The third check-sat then encoded a[j] eagerly, with a congruence chain
; that never mentions the lazy base row, and skipped read refinement: it
; answered sat to a[i] = 1, a[j] = 2, i = j.
(set-logic QF_ABV)
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun x () (Array (_ BitVec 12) (_ BitVec 15)))
(declare-fun x1 () (Array (_ BitVec 12) (_ BitVec 15)))
(declare-fun b () (Array (_ BitVec 12) (_ BitVec 15)))
(declare-fun b6 () (Array (_ BitVec 16) (_ BitVec 8)))
(declare-fun v () (_ BitVec 2))
(assert (= (select a i) #x1))
(assert (distinct (distinct (_ bv0 4) ((_ zero_extend 2) v)) (not (= b (store b ((_ zero_extend 4) (select b6 (_ bv0 16))) (_ bv0 15))))))
(push 1)
; CHECK: ^sat$
(check-sat)
(assert (distinct x x1 (store b ((_ sign_extend 10) ((_ zero_extend 1) ((_ extract 1 1) v))) (_ bv0 15))))
; CHECK: ^sat$
(check-sat)
(pop 1)
(push 1)
(assert (and (= (select a j) #x2) (= i j)))
; CHECK: ^unsat$
(check-sat)
(pop 1)
(push 1)
(assert (= (select a j) #x2))
; CHECK: ^sat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
