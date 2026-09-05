; RUN: %solver -d %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A three-operand bvmul parses into a single n-ary node, survives
; simplification and bit-blasts whole. -d rebuilds the model against the
; original query, so a dropped operand anywhere down the pipeline fails.
(set-logic QF_BV)
(declare-const a (_ BitVec 4))
(declare-const b (_ BitVec 4))
(declare-const c (_ BitVec 4))
(assert (= (bvmul a b c) (_ bv8 4)))
(assert (bvugt a (_ bv1 4)))
(assert (bvugt b (_ bv1 4)))
(check-sat)
