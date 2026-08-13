; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --array-equality -d %s | %OutputCheck %s
;
; Read-over-write muxes whose every leaf is a packed circuit: the stored
; values are lowered floating-point operations, and the residual read at the
; bottom of the expansion folds into one of them, so no node of the array
; transform's mux carries the element format at all -- there is nothing to
; stamp and nothing to derive from. The native gate must therefore not admit
; a read over a WRITE in the first place; with it admitted, the surviving
; classifications hit the bit-blaster's source-sort assertion (garbage
; widths in release). The arrays are also float-INDEXED, so the store and
; select indexes are packed floats themselves.
;
; Found by fuzzing QF_ABVFP with float-sorted arrays, reduced with ddSMT.
;
; CHECK: ^sat
(set-logic QF_ABVFP)
(declare-const x (Array Float128 Float64))
(declare-const x9 (Array Float128 Float64))
(declare-const x6 Float128)
(declare-fun v () Float128)
(declare-fun r () RoundingMode)
(declare-fun a () (Array Float128 Float64))
(assert (ite (fp.lt (select x9 (fp (_ bv0 1) (_ bv0 15) (_ bv0 112))) (select (store x9 x6 (select x9 (fp (_ bv0 1) (_ bv32767 15) (_ bv1 112)))) (fp (_ bv0 1) (_ bv0 15) (_ bv0 112))) (select (store x9 x6 (select a (fp (_ bv0 1) (_ bv0 15) (_ bv0 112)))) (fp (_ bv0 1) (_ bv0 15) (_ bv0 112)))) (and true true (fp.isSubnormal (select x9 (fp (_ bv1 1) (_ bv0 15) (_ bv0 112)))) (fp.isSubnormal (select x (fp (_ bv0 1) (_ bv0 15) (_ bv0 112)))) (fp.isPositive (select (store (store x9 v (fp.mul r (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)) (select x9 (fp (_ bv1 1) (_ bv1 15) (_ bv0 112))))) (fp (_ bv0 1) (_ bv0 15) (_ bv0 112)) (fp.abs (select x9 (fp (_ bv0 1) (_ bv1 15) (_ bv1 112))))) v))) false))
(check-sat)
(exit)
