; RUN: %solver --uninterpreted-functions --ackermanize --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --ackermanize --incremental=on %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; --ackermanize eagerly compiles arrays only; it does not route UF through the
; array transform. UF congruence remains governed by its own eager policy and
; dynamic checker.
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (= i j))
(assert (distinct (f (select a i)) (f (select a j))))
(check-sat)
