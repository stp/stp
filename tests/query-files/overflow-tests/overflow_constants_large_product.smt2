; RUN: %solver %s | %OutputCheck %s
; Regression test: constant folding of bvumulo used to abort with
; "BVConstEvaluator:numeric overflow error" whenever the exact product
; reached 2^(2w-1), because the 2w-bit intermediate was multiplied with
; the signed, strict-overflow BitVector_Multiply.
(set-logic QF_BV)
; 11585^2 = 134212225 < 2^27: never crashed, overflows 14 bits.
(assert (bvumulo (_ bv11585 14) (_ bv11585 14)))
; 11586^2 = 134235396 >= 2^27: smallest square past the old crash boundary.
(assert (bvumulo (_ bv11586 14) (_ bv11586 14)))
; Maximal operands.
(assert (bvumulo (_ bv16383 14) (_ bv16383 14)))
(assert (bvumulo #xFF #xFF))
; Small product: no overflow.
(assert (not (bvumulo (_ bv3 14) (_ bv5 14))))
; Signed cases with most-negative operands.
(assert (bvsmulo #x80 #x80))
(assert (bvsmulo (_ bv8192 14) (_ bv8192 14)))
(assert (not (bvsmulo #xFF #x02)))
; CHECK-NEXT: ^sat
(check-sat)
(exit)
