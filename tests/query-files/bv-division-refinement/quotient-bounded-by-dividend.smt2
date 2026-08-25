; A quotient cannot exceed its dividend once the divisor is non-zero. Without
; that fact the abstraction has nothing to say about a 256-bit division: it
; spends its blocking lemmas one operand pair at a time and then encodes the
; divider exactly, which does not finish. Timed at 60s before the fact
; existed; milliseconds after.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (distinct b (_ bv0 256)))
(assert (bvugt (bvudiv a b) a))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
