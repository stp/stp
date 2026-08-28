; A memory-relief rebuild rotates the complete AIG/abstraction identity epoch.
; The first disposable level forces that rotation. In the fresh epoch the
; second level creates an inner multiplication, and the third reuses it below
; a new multiplication. Re-harvested IDs, root owners and dependency edges
; must all belong to the new epoch and close to the final unsatisfiable answer.
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
; EXACT-NEXT: ^sat$
; EXACT-NEXT: ^unsat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))

(push 1)
(assert (= ((_ extract 0 0) (bvmul a #x03)) #b1))
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
