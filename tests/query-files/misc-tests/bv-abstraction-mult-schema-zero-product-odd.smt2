; An odd bit-vector is invertible modulo 2^W. Therefore an odd x and a
; nonzero s cannot have a zero truncated product. MUL8 expresses the same
; fact as
;
;   s = s << (x & (1 >> t)), where t = x * s.
;
; The shift amount is nonzero only when t is zero and x is odd, and in that
; case s = s << 1 has only the all-zero solution. The refiner installs that
; compact implication rather than constructing the two variable shifts.
;
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-schema-groups=mul8 %s 2>&1 | %OutputCheck %s
; How many operations that round refines is not pinned: it is whatever the
; candidate happened to contradict, and a different SAT backend returns a
; different candidate. CaDiCaL 3.0.1 refines one here and 2.1.3 refines two,
; both having installed the fact this test is about.
; CHECK: BV abstraction: BVMULT factor-unchanged-by-masked-shift lemma over operand [01]
; CHECK-NEXT: BV abstraction: refined [0-9]+ operations
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 256))
(declare-fun s () (_ BitVec 256))
(assert
  (let ((t (bvmul x s)))
    (distinct s (bvshl s (bvand x (bvlshr (_ bv1 256) t))))))
(check-sat)
(exit)
