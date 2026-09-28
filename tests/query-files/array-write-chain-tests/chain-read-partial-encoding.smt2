; RUN: %solver --array-equality -d %s | %OutputCheck %s
;
; A chain read whose value only reaches the encoding through an extract:
; the bits the extract does not take are never bit-blasted, so the row
; symbol's SAT binding has holes. The array-equality route reaches read
; refinement through the exact-stack driver, which totalised the batch
; table's READ rows only -- emitChainReadLemmas then handed getEquals a
; bit with no SAT variable and the solve died on "Incremental array
; refinement has an incomplete SAT binding for an axiom leaf". The chain
; rows have to be totalised there too; an unencoded bit is unconstrained,
; and a fresh variable is exactly what the blasted formula means by it.
;
; Reduced from a fuzzsmt QF_ABVFP query. The push/pop cycle matters: the
; row is only half-encoded once the chain has been folded and unfolded
; across levels, so the failure lands several check-sats in.
;
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
(set-logic  QF_ABVFP)
(set-info :status unknown)
(declare-fun v0 () Float128)
(declare-fun v1 () (_ FloatingPoint 15 113))
(declare-fun v2 () (_ FloatingPoint 15 113))
(declare-fun v3 () (_ FloatingPoint 15 113))
(declare-fun v4 () (_ FloatingPoint 8 24))
(declare-fun rm5 () RoundingMode)
(declare-fun v6 () (_ BitVec 14))
(declare-fun a7 () (Array (_ FloatingPoint 15 113) (_ BitVec 1)))
(declare-fun a8 () (Array (_ FloatingPoint 15 113) (_ FloatingPoint 15 113)))
(declare-fun a9 () (Array (_ BitVec 6) (_ FloatingPoint 15 113)))
(define-fun __fuzz_q () Bool
(let ((e0 ((_ to_fp 15 113) #b00001011110000000111101111111111010011000001101011010111101101011000001110101010001101011001110000111110011011001010010010111100)))
(let ((e1 ((_ to_fp 15 113) rm5 (_ bv1 1))))
(let ((e2 (_ bv0 4)))
(let ((e3 (bvlshr v6 ((_ zero_extend 10) e2))))
(let ((e4 (store a9 ((_ extract 11 6) v6) e1)))
(let ((e5 (store a8 v2 e0)))
(let ((e6 (store e5 e0 v0)))
(let ((e7 (select a9 ((_ extract 5 0) v6))))
(let ((e8 (select e6 e0)))
(let ((e9 (select e4 ((_ sign_extend 2) e2))))
(let ((e10 (select a8 v2)))
(let ((e11 (store e6 v2 e7)))
(let ((e12 (store e11 v1 e8)))
(let ((e13 ((_ to_fp_unsigned 5 11) roundTowardNegative e3)))
(let ((e14 (fp.sub RTZ e9 ((_ to_fp 15 113) RNA v4))))
(let ((e15 (fp.max e10 ((_ to_fp 15 113) RTZ e13))))
(let ((e16 (fp.abs e0)))
(let ((e17 (store e12 e14 e16)))
(let ((e18 (store e17 v3 e0)))
(let ((e19 (store e6 e15 e1)))
(let ((e20 (select e18 e15)))
(let ((e21 true))
(let ((e22 (fp.isNormal e20)))
(let ((e23 true))
(let ((e24 true))
(let ((e25 true))
(let ((e26 false))
(let ((e27 true))
(let ((e28 true))
(let ((e29 (distinct e19 e5)))
(let ((e30 (and e22 e27 e25)))
(let ((e31 (ite e29 e29 e26)))
(let ((e32 true))
(let ((e33 (not e30)))
(let ((e34 (= e23 e33 e21)))
(let ((e35 (xor e24 e32 e34)))
(let ((e36 (=> e28 e31)))
(let ((e37 false))
(let ((e38 (or e36 e37)))
(let ((e39 true))
(let ((e40 (xor e39 e35)))
(let ((e41 (= e40 e38 e38)))
e41
)))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(push 1)
(assert __fuzz_q)
(check-sat)
(pop 1)
(push 1)
(assert (not __fuzz_q))
(check-sat)
(pop 1)
(push 1)
(assert __fuzz_q)
(check-sat)
(pop 1)
(push 1)
(assert (not __fuzz_q))
(check-sat)
(pop 1)
(push 1)
(assert __fuzz_q)
(check-sat)
(pop 1)
(push 1)
(assert (not __fuzz_q))
(check-sat)
(pop 1)
(push 1)
(assert __fuzz_q)
(check-sat)
(pop 1)
(push 1)
(assert (not __fuzz_q))
(check-sat)
(pop 1)
(assert __fuzz_q)
(check-sat)
