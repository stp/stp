; RUN: %solver %s | %OutputCheck %s
;
; The same overflowing fused multiply-add reached through symbols the
; substitution pass resolves to literals, so the folder runs after
; preprocessing rather than in the parser.
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 3 9))
(declare-const y (_ FloatingPoint 3 9))
(declare-const z (_ FloatingPoint 3 9))
(assert (= x (fp #b1 #b110 #b11111111)))
(assert (= y (fp #b1 #b110 #b11111111)))
(assert (= z (_ +zero 3 9)))
(assert (= (fp.fma RNA x y z) (_ +oo 3 9)))
(check-sat)
