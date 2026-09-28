; An assertion that occurs inside another one is true there too, so the
; disjunction it sits in collapses rather than being bit-blasted a second
; time.
; RUN: %solver -s --embedded-constraints=1 %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun p () (_ BitVec 32))
(declare-fun q () (_ BitVec 32))
(declare-fun r () (_ BitVec 32))
(assert (bvult p q))
(assert (or (bvult p q) (bvugt r (_ bv1000 32))))
(assert (distinct r (_ bv5 32)))
; CHECK: After Embedded Constraints
; CHECK: ^sat
(check-sat)
(exit)
