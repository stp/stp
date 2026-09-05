; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; A float is implemented by packed bits inside STP, but that representation is
; not an implicit SMT-LIB cast. fp.to_ieee_bv is the explicit route to BV ops.
; CHECK: bitvector operator requires bitvector operands
(set-logic QF_BVFP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= (bvnot x) #x00000000))
(check-sat)
