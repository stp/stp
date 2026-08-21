; RUN: %solver --uninterpreted-functions --ackermanize --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --ackermanize --incremental=on %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; GATE-03 boundary: --ackermanize eagerly compiles ARRAYS only; UF
; stays on the dynamic reference profile and still refines.
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (= i j))
(assert (distinct (f (select a i)) (f (select a j))))
(check-sat)
