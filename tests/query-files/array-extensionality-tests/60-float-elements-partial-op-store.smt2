; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A partial floating-point operation (fp.max, fp.fma) inside a store
; equated with another array: the equality's operands are abstracted
; out of the input formula when the equality is built, so the pass
; that makes partial operations total never saw them, and the
; two-child fp.max reached the float blaster and crashed the solve.
(set-logic QF_ABVFP)
(declare-fun x5 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)))
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun x2 () (Array (_ BitVec 8) (_ FloatingPoint 8 24)))
(assert (= x5 (store x2 (_ bv0 8)
                (fp.max (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))
                        (fp.fma RTN (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))
                                (_ +zero 8 24) x)))))
(check-sat)
