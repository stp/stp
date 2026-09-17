; A shift left by a constant and the multiply it equals are the same
; coefficient, so `(x << 2) udiv y` and `(x * 4) udiv y` are one division.
; The front ends spell a constant shift as concat(extract(x, w-3, 0), 0_2),
; which is why the combination has to read that shape as a coefficient.
;
; A power-of-two coefficient is written back as the shift rather than as the
; product: the shift is wiring, the product a circuit, and the rest of the
; simplifier recognises shifts. The pass is still canonical either way --
; one spelling per coefficient -- and this checks it picked one.
; RUN: %solver -s --linear-form=1 %s 2>&1 | %OutputCheck %s
; CHECK: Terms given a canonical form:[1-9]
; CHECK: ^unsat$
;
; RUN: %solver %s | %OutputCheck --check-prefix=OFF %s
; OFF: ^unsat$
;
; Nothing is expanded when a combination is wider than the limit allows, so
; the query keeps the spelling it arrived with and the answer is unchanged.
; RUN: %solver --linear-form=1 --linear-form-addend-limit=0 %s | %OutputCheck --check-prefix=OFF %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert
  (not (=
    (bvudiv (bvshl x (_ bv2 32)) y)
    (bvudiv (bvmul (_ bv4 32) x) y))))
(check-sat)
(exit)
