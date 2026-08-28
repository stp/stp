; Proxy definitions carry provenance but are not themselves semantic owners.
;
; The first solve creates nested multiplications separated by BVNOT, which
; forces operand proxy CIs. After that level is popped, three unrelated solves
; must not refine either dormant record merely because the proxy
; biconditionals are permanent. The final solve reactivates the same composite
; root and must recover the inner producer through the proxy provenance and
; dependency closure, making the contradictory stack unsatisfiable.
;
; RUN: %solver --incremental=on -s --disable-simplifications --bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-schemas=0 --bv-term-abstraction-rounds=20 %s 2>&1 | %OutputCheck --check-prefix=SCOPED %s
;
; SCOPED: ^sat$
; SCOPED-NOT: BV abstraction:
; SCOPED: ^sat$
; SCOPED-NOT: BV abstraction:
; SCOPED: ^sat$
; SCOPED-NOT: BV abstraction:
; SCOPED: ^sat$
; SCOPED: ^unsat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))

(push 1)
(assert (= x #x01))
(assert (= y #x01))
(assert (= w #x01))
(assert (= ((_ extract 0 0) (bvmul (bvnot (bvmul x y)) w)) #b0))
(check-sat)
(pop 1)

(push 1)
(assert (= x #x00))
(assert (= y #x01))
(assert (= w #x01))
(check-sat)
(pop 1)

(push 1)
(assert (= x #x02))
(assert (= y #x03))
(assert (= w #x05))
(check-sat)
(pop 1)

(push 1)
(assert (= x #x07))
(assert (= y #x0b))
(assert (= w #x0d))
(check-sat)
(pop 1)

(push 1)
(assert (= x #x00))
(assert (= y #x01))
(assert (= w #x01))
(assert (= ((_ extract 0 0) (bvmul (bvnot (bvmul x y)) w)) #b0))
(check-sat)
(pop 1)
(exit)
