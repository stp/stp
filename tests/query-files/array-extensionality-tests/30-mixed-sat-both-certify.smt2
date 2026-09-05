; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The active checker owns both components of one assignment: v is forced
; to 42 through cross-array congruence over the true equality, and w is
; forced to 5 through same-array congruence on disconnected c. Its
; certified observation batch must make the distinct hold in the model.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(declare-fun k () (_ BitVec 4))
(declare-fun l () (_ BitVec 4))
(declare-fun v () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (= a b))
(assert (= i j))
(assert (= (select a i) #x2a))
(assert (= (select b j) v))
(assert (not (bvult k l)))
(assert (not (bvult l k)))
(assert (= (select c k) #x05))
(assert (= (select c l) w))
(assert (distinct v w))
(check-sat)
