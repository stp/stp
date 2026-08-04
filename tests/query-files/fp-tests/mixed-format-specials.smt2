; RUN: %solver %s | %OutputCheck %s
;
; Special values of different formats must coexist in one problem. They used
; to be childless nodes, whose hash-cons identity is (kind, children) alone --
; so every format's NaN was ONE shared node, re-stamped by whichever format
; parsed last, and a file mixing formats crashed the blaster on the widths
; (silently wrong under NDEBUG). They are packed interned constants now, one
; node per format.
(set-logic QF_FP)
(set-option :produce-models true)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 5 11))
(declare-fun z () (_ FloatingPoint 3 5))
(assert (= x (_ NaN 8 24)))
(assert (fp.isNaN x))
(assert (= y (_ +oo 5 11)))
(assert (= z (_ -zero 3 5)))
; CHECK: ^sat
(check-sat)
; The infinity and the signed zero are unique bit patterns. NaN's payload is
; deliberately not pinned here: SMT '=' makes every NaN equal to every other,
; so x is constrained through fp.isNaN above instead.
; CHECK-L: |y| (fp #b0 #b11111 #b0000000000)
; CHECK-L: |z| (fp #b1 #b000 #b0000)
(get-value (y z))
