; RUN: %solver %s | %OutputCheck %s
; CHECK: ^sat
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)

; x's only use is a chain of operations against constants under a
; predicate against a constant. The ground-path collapse in
; RemoveUnconstrained replaces the predicate with a fresh boolean and
; records a witness definition for x, so this never reaches the SAT
; solver as a 128-bit multiply-free modulo circuit.
(declare-fun x () (_ BitVec 128))
(assert (= (bvurem x (_ bv100 128)) (_ bv42 128)))

; A second, layered one: ((y >> 3) + 5) >u 20.
(declare-fun y () (_ BitVec 128))
(assert (bvugt (bvadd (bvlshr y (_ bv3 128)) (_ bv5 128)) (_ bv20 128)))

; And a masked one, through the sample fallback: (z & 0x55) == 0x41.
(declare-fun z () (_ BitVec 128))
(assert (= (bvand z (_ bv85 128)) (_ bv65 128)))

(check-sat)
(exit)
