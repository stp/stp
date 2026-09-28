; RUN: %solver --uninterpreted-functions --incremental=on %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^sat
;
; An ordinary first solve sigma0-eliminates x through the base equation.  A
; later UF-active exact-stack round uses x only as a leaf actual after scoped
; preprocessing removes every other occurrence.  UF scalar totalization must
; restore x's defining equation before allocating its SAT bits.
(set-logic QF_AUFBV)
(declare-fun x () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun g ((_ BitVec 8) (_ BitVec 8)) Bool)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= x w))
(check-sat)
(push 1)
(assert (not (= w w)))
(check-sat)
(assert (= y (f (bvadd w x))))
(check-sat)
(pop 1)
(assert (g (bvadd (select a w) x) x))
(check-sat)
