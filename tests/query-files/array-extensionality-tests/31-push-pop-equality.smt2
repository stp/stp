; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^unsat
; An equality asserted under a pushed scope: unsat while it is in force, sat
; again after the pop. Generated records and witness bundles are solve-local,
; so the middle solve lowers no equality at all. Re-asserting the durable
; opaque equality creates a fresh record for the third solve and turns the
; verdict back.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (distinct (select a #b00) (select b #b00)))
(push 1)
(assert (= a b))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (= a b))
(check-sat)
(pop 1)
