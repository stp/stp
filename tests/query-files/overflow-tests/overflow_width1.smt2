; RUN: %solver %s | %OutputCheck %s
; Each overflow predicate is checked against its own definition at width 1,
; under its own (check-sat), so a predicate that stops agreeing turns its
; query sat instead of hiding behind the other five.
(set-logic QF_BV)
(declare-fun a () (_ BitVec 1))
(declare-fun b () (_ BitVec 1))

(push 1)
(assert (not (= (bvnego a) (= a #b1))))
; CHECK: ^unsat
(check-sat)
(pop 1)

(push 1)
(assert (not (= (bvuaddo a b) (bvult (bvadd a b) a))))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)

(push 1)
(assert (not (= (bvsmulo a b)
  (let ((p (bvmul ((_ sign_extend 1) a) ((_ sign_extend 1) b))))
    (distinct p ((_ sign_extend 1) ((_ extract 0 0) p)))))))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)

(push 1)
(assert (not (= (bvusubo a b) (bvult a b))))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)

(push 1)
(assert (not (= (bvsdivo a b) (and (= a #b1) (= b #b1)))))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)

(push 1)
(assert (not (= (bvssubo a b)
  (let ((d (bvsub ((_ sign_extend 1) a) ((_ sign_extend 1) b))))
    (distinct ((_ extract 1 1) d) ((_ extract 0 0) d))))))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(exit)
