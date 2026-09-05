; RUN: %solver %s 2>&1 | %OutputCheck %s
; RUN: %solver %s 2>&1 | %OutputCheck --check-prefix=NOHINT %s
;
; The gate exists so that a non-FP benchmark can own these names, and files
; that do have parsed since before STP had floating-point support at all. The
; hint must not cost them that: every name below resolves to the bitvector
; this file declared, so the file still solves and says nothing about floats.
;
; The second pass is what makes the negative check mean anything. A CHECK-NOT
; searches the region *between* its neighbouring matches, so pairing it with
; the CHECK-L below would leave it an empty region to search; alone under its
; own prefix it sees the whole output.
; CHECK-L: sat
; NOHINT-NOT-L: is a floating-point name
(set-logic QF_BV)
(declare-fun fp () (_ BitVec 8))
(declare-fun NaN () (_ BitVec 8))
(declare-fun RNE () (_ BitVec 8))
(declare-fun Float64 () (_ BitVec 8))
(assert (= fp NaN))
(assert (= RNE Float64))
(check-sat)
