; A memory-relief rebuild rotates the complete AIG/abstraction identity epoch.
; Nine disposable levels force that rotation deterministically: each level's
; popped DAG retires its nodes from the semantic cache (the limit of one
; below), and nine of them exceed the four-to-one deadness ratio whatever the
; SAT backend's models did -- the abstraction's own refinement may rotate the
; epoch earlier on some backends, which the checks below are indifferent to.
; In the fresh epoch the next level creates an inner multiplication, and the
; last reuses it below a new multiplication. Re-harvested IDs, root owners
; and dependency edges must all belong to the new epoch and close to the
; final unsatisfiable answer.
;
; RUN: %solver --incremental=on -s --incremental-semantic-cache-limit=1 --incremental-reencode-limit=1 --disable-simplifications --bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-schemas=0 --bv-term-abstraction-rounds=4 %s 2>&1 | %OutputCheck --check-prefix=REBUILD %s
; RUN: %solver --incremental=off --disable-simplifications %s 2>&1 | %OutputCheck --check-prefix=EXACT %s
;
; REBUILD: ^sat$
; REBUILD: encoding epoch reset
; REBUILD: ^sat$
; REBUILD: ^unsat$
;
; EXACT: ^sat$
; EXACT: ^sat$
; EXACT: ^sat$
; EXACT: ^sat$
; EXACT: ^sat$
; EXACT: ^sat$
; EXACT: ^sat$
; EXACT: ^sat$
; EXACT: ^sat$
; EXACT: ^sat$
; EXACT: ^unsat$
(set-logic QF_BV)
(declare-fun a1 () (_ BitVec 8))
(declare-fun a2 () (_ BitVec 8))
(declare-fun a3 () (_ BitVec 8))
(declare-fun a4 () (_ BitVec 8))
(declare-fun a5 () (_ BitVec 8))
(declare-fun a6 () (_ BitVec 8))
(declare-fun a7 () (_ BitVec 8))
(declare-fun a8 () (_ BitVec 8))
(declare-fun a9 () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(push 1)
(assert (= ((_ extract 0 0) (bvmul a1 #x03)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= ((_ extract 0 0) (bvmul a2 #x03)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= ((_ extract 0 0) (bvmul a3 #x03)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= ((_ extract 0 0) (bvmul a4 #x03)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= ((_ extract 0 0) (bvmul a5 #x03)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= ((_ extract 0 0) (bvmul a6 #x03)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= ((_ extract 0 0) (bvmul a7 #x03)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= ((_ extract 0 0) (bvmul a8 #x03)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= ((_ extract 0 0) (bvmul a9 #x03)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= x #x01))
(assert (= y #x01))
(assert (= ((_ extract 0 0) (bvmul x y)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= x #x00))
(assert (= y #x01))
(assert (= w #x01))
(assert (= ((_ extract 0 0) (bvmul (bvmul x y) w)) #b1))
(check-sat)
(pop 1)
(exit)
