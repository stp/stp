; Boolean array operands retain their source sorts and use a two-element
; domain, including reads used as indices and values of other arrays.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=off %s | %OutputCheck %s
; RUN: %solver --array-ackermann-budget=0 %s | %OutputCheck %s
; RUN: %solver --ackermanize %s | %OutputCheck %s
(set-logic ALL)
(declare-const a (Array Bool Bool))
(declare-const b (Array Bool Bool))
(declare-const p Bool)
(declare-const q Bool)
(assert (select a false))
(assert (not (select a true)))
; CHECK-NEXT: ^sat$
(check-sat)
(push 1)
(assert (= (select a p) p))
; CHECK-NEXT: ^unsat$
(check-sat)
(pop 1)
(assert (= (select b false) (select a false)))
(assert (= (select b true) (select a true)))
(push 1)
(assert (distinct a b))
; CHECK-NEXT: ^unsat$
(check-sat)
(pop 1)
; CHECK-NEXT: ^sat$
(check-sat)
(push 1)
(assert (distinct (select (store (ite p a b) q (select a p)) q)
                  (select a p)))
; CHECK-NEXT: ^unsat$
(check-sat)
(pop 1)
(assert (select a (select a false)))
; CHECK-NEXT: ^unsat$
(check-sat)

(reset)
(set-logic ALL)
(declare-const flags (Array (_ BitVec 8) Bool))
(declare-const bytes (Array Bool (_ BitVec 8)))
(declare-const x (_ BitVec 8))
(assert (= (select bytes true) x))
(assert (select flags x))
; CHECK-NEXT: ^sat$
(check-sat)
(assert (not (select flags (select bytes true))))
; CHECK-NEXT: ^unsat$
(check-sat)

(reset)
(set-logic ALL)
(declare-const a (Array Bool Bool))
(assert (= a ((as const (Array Bool Bool)) false)))
(assert (select (store a true true) true))
(assert (not (select (store a true true) false)))
; CHECK-NEXT: ^sat$
(check-sat)
(assert (distinct (store (store a false true) true true)
                  ((as const (Array Bool Bool)) true)))
; CHECK-NEXT: ^unsat$
(check-sat)
