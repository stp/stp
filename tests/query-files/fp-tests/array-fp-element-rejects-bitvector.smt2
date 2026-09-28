; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)

; An FP element is not interchangeable with its packed bit-vector carrier.
; CHECK: stored value is not a float of the declared format
(declare-fun a () (Array (_ BitVec 1) (_ FloatingPoint 8 24)))
(assert (fp.isZero (select (store a #b0 #x00000000) #b0)))
(check-sat)
