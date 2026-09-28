; RUN: %solver -d %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A wide product of single-use variables ranges over every value, so
; unconstrained-variable elimination solves this without bit-blasting a
; single multiplier -- as it always has for the binarised form. -d then
; rebuilds the model through the recorded substitutions and re-checks the
; original query, which exercises the counterexample path of the rule.
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const c (_ BitVec 32))
(assert (= (bvmul a b c #x00000007) #x12345678))
(check-sat)
