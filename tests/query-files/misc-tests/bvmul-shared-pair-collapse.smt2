; RUN: %solver -s %s 2>&1 | %OutputCheck %s
; RUN: %solver -d %s | %OutputCheck --check-prefix=MODEL %s
; CHECK: BVMULT applications saved:1
; CHECK: ^sat
; MODEL: ^sat
; The pair {a, b} occurs only inside these two products. Sub-term
; extraction gives (bvmul a b) a node of its own, and unconstrained
; elimination then collapses it to a fresh variable: one multiplier is
; never built at all, and the model for a and b is reconstructed through
; the recorded substitutions, which -d re-checks.
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const c (_ BitVec 32))
(declare-const d (_ BitVec 32))
(assert (= (bvmul a b c) #x12345678))
(assert (= (bvmul a b d) #x87654321))
(check-sat)
