; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK: define-fun \|a\| \(\) \(Array RoundingMode \(_ BitVec 8\)\).*as const \(Array RoundingMode \(_ BitVec 8\)\).*RTZ #x2A
; CHECK: define-fun \|c\| \(\) \(Array \(_ BitVec 2\) RoundingMode\).*as const \(Array \(_ BitVec 2\) RoundingMode\)\) RNE.*#b01 RTN
; get-model prints RoundingMode index and element sorts true to the
; declaration, with mode names for indexes and cells (RNE for the
; unobserved cells), so the define-funs replay.
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-fun a () (Array RoundingMode (_ BitVec 8)))
(declare-fun b () (Array RoundingMode (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 2) RoundingMode))
(assert (not (= a b)))
(assert (= (select a RTZ) #x2a))
(assert (= (select c #b01) RTN))
(check-sat)
(get-model)
