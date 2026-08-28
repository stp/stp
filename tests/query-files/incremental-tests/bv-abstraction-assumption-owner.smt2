; check-sat-assuming roots own abstractions only for the solve that activates
; them. The first assumption commits and refines the multiplication. The
; following plain check must not keep that record live, while a later
; assumption over the canonical same result must reactivate it and prove the
; contradictory requested bit unsatisfiable.
;
; RUN: %solver --incremental=on -s --disable-simplifications --bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-schemas=0 --bv-term-abstraction-rounds=20 %s 2>&1 | %OutputCheck --check-prefix=SCOPED %s
;
; SCOPED: ^sat$
; SCOPED-NOT: BV abstraction:
; SCOPED: ^sat$
; SCOPED: ^unsat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= x #x00))
(assert (= y #x01))
(check-sat-assuming ((= ((_ extract 0 0) (bvmul x y)) #b0)))
(check-sat)
(check-sat-assuming ((= ((_ extract 0 0) (bvmul x y)) #b1)))
(exit)
