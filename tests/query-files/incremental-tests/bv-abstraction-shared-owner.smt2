; One abstraction producer can be owned by more than one active assertion.
; The first disjunction can avoid its multiplication constraint by choosing
; p=true. The second can avoid the same constraint only with p=false, so with
; both roots active the real product bit is forced to zero and the stack is
; unsatisfiable. Popping either owner must leave the record attached to the
; other root rather than retiring it globally.
;
; RUN: %solver --incremental=on --disable-simplifications --bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-schemas=0 --bv-term-abstraction-rounds=4 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off --disable-simplifications %s 2>&1 | %OutputCheck --check-prefix=EXACT %s
;
; ABSTRACTED: ^sat$
; ABSTRACTED-NEXT: ^unsat$
; ABSTRACTED-NEXT: ^sat$
; ABSTRACTED-NEXT: ^sat$
;
; EXACT: ^sat$
; EXACT-NEXT: ^unsat$
; EXACT-NEXT: ^sat$
; EXACT-NEXT: ^sat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun p () Bool)
(assert (= x #x01))
(assert (= y #x01))

(push 1)
(assert (or p (= ((_ extract 0 0) (bvmul x y)) #b0)))
(check-sat)

(push 1)
(assert (or (not p) (= ((_ extract 0 0) (bvmul x y)) #b0)))
(check-sat)
(pop 1)

(check-sat)
(pop 1)
(check-sat)
(exit)
