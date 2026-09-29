; RUN: not %solver %s 2>&1 | %OutputCheck %s
; RUN: not %solver %s 2>&1 | %OutputCheck --check-prefix=NOANSWER %s
;
; A Real constant converts to a float; a symbolic Real has no conversion,
; and is refused rather than read as something else.
; CHECK: to_fp of a symbolic Real is not supported
; NOANSWER-NOT: ^sat$
; NOANSWER-NOT: ^unsat$
(set-logic QF_BVFPLRA)
(declare-fun r () Real)
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= y ((_ to_fp 8 24) RNE r)))
(check-sat)
