; RUN: %solver %s | %OutputCheck %s
; CHECK: ^sat
;
; Regression test for Simplifier::PullUpITE dropping a floating-point
; format stamp.  The canonicalised index of a float-indexed array is a
; bitvector circuit carrying the index's float format as a stamp (see
; FpTotalise); simplifying it can meet a concatenation of two
; if-then-elses over one condition, which PullUpITE rebuilds as one
; if-then-else over two concatenations -- without the stamp, changing
; the node's type from floating-point to bitvector and failing
;   Assertion `result.GetType() == in.GetType()'
; in builds with assertions (silent stamp loss otherwise).
;
; Satisfiable: fp.rem of -zero by a normal w is -zero, so the select
; at the NaN literal misses the store and reads an unconstrained cell.
;
; Found by differential fuzzing against z3; delta-minimized with ddSMT.
(set-logic QF_ABVFP)
(declare-fun b () (Array Float16 (_ BitVec 5)))
(declare-fun w () Float16)
(assert (= (_ bv0 5)
           (select (store b (fp.rem (_ -zero 5 11) w) (_ bv1 5))
                   (_ NaN 5 11))))
(check-sat)
