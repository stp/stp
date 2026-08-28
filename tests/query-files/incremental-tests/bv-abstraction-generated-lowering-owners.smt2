; Root ownership follows the AIG actually committed, not an AST-only walk.
; The bit-blaster lowers n-ary addition/multiplication to fresh binary ASTs
; and translates signed division into a generated ITE/unsigned-operation DAG.
; None of those abstraction-producing nodes is a child of the source root.
; Provenance on their result CIs still attaches each producer transactionally
; to the encoded root, so all three contradictory queries are refined.
;
; RUN: %solver --incremental=on --disable-simplifications --bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-schemas=0 --bv-term-abstraction-rounds=4 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off --disable-simplifications %s 2>&1 | %OutputCheck --check-prefix=EXACT %s
;
; ABSTRACTED: ^unsat$
; ABSTRACTED-NEXT: ^unsat$
; ABSTRACTED-NEXT: ^unsat$
;
; EXACT: ^unsat$
; EXACT-NEXT: ^unsat$
; EXACT-NEXT: ^unsat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))

(push 1)
(assert (= x #x00))
(assert (= y #x01))
(assert (= z #x01))
(assert (= ((_ extract 0 0) (bvmul x y z)) #b1))
(check-sat)
(pop 1)

(push 1)
(assert (= x #x00))
(assert (= y #x00))
(assert (= z #x00))
(assert (= ((_ extract 0 0) (bvadd x y z)) #b1))
(check-sat)
(pop 1)

(push 1)
(assert (= x #x00))
(assert (= y #x01))
(assert (= (bvsdiv x y) #x01))
(check-sat)
(pop 1)
(exit)
