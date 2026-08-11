; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^\($
; CHECK: define-fun \|A\| \(\) \(Array \(_ BitVec 2\) \(_ BitVec 2\)\).*#b00 #b10\).*#b01 #b11\)
; A substituted symbol holds exactly what its definition holds: its
; printed interpretation carries the write's cell (1 -> 3) and the
; base's observed cell (0 -> 2), in ascending index order.
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-fun A () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun B () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (= A (store B (_ bv1 2) (_ bv3 2))))
(assert (= (select B (_ bv0 2)) (_ bv2 2)))
(check-sat)
(get-model)
