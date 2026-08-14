; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
;
; The less-than comparisons mirror onto the greater-thans at node creation,
; the way BVLT mirrors onto BVGT: fp.lt(a, b) = fp.gt(b, a) and
; fp.leq(a, b) = fp.geq(b, a), exactly, NaN included.
;
; Each xor pairs a comparison with its mirror, so each is unsatisfiable on
; its own -- and the two RUN lines check that for different reasons.
; With simplification, both xor operands intern as the SAME node and the
; factory collapses xor(n, n) to false before any circuit exists, so
; --exit-after-CNF still prints its verdict: that run passes only while the
; mirror rule fires. With --disable-simplifications the hashing factory
; keeps all four comparison kinds, both circuits are built, and the SAT
; solver proves the semantic identity the rule relies on.
;
; One (check-sat) per mirror, so a rule that stops firing for just one of
; the two pairs turns that query sat instead of hiding behind the other.
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 3 5))
(declare-fun b () (_ FloatingPoint 3 5))

; fp.lt(a, b) = fp.gt(b, a)
(push 1)
(assert (xor (fp.lt a b) (fp.gt b a)))
; CHECK: ^unsat
(check-sat)
(pop 1)

; fp.leq(a, b) = fp.geq(b, a)
(push 1)
(assert (xor (fp.leq a b) (fp.geq b a)))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(exit)
