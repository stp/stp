; RUN: %solver %s | %OutputCheck %s
; The assertion is stored as one three-operand bvmul; the SMT-LIB printer
; chunks n-ary operators into a chain of binary applications, as it always
; has for bvadd, so SMT-LIB1 consumers never see a wide application.
; CHECK: bvmul \S+ \(bvmul
; CHECK: ^sat
(set-logic QF_BV)
(declare-const a (_ BitVec 4))
(declare-const b (_ BitVec 4))
(declare-const c (_ BitVec 4))
(assert (= (bvmul a b c) (_ bv8 4)))
(get-assertions)
(check-sat)
