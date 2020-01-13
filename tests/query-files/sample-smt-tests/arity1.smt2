; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
; CHECK-NEXT: ^unsat
(set-info :status unsat)

; distinct is pairwise

(declare-const u (_ BitVec 2))
(declare-const v (_ BitVec 2))
(declare-const w (_ BitVec 2))
(declare-const x (_ BitVec 2))
(declare-const y (_ BitVec 2))

; unsat by pigeon hole.	
(assert (distinct u v w x y))

(check-sat)
