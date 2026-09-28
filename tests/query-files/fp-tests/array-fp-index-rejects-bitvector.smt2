; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)

; Packed-width equality is not a source-language coercion from BitVec to FP.
; CHECK: array index is not a float of the declared format
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 1)))
(assert (= (select a #x00000000) #b0))
(check-sat)
