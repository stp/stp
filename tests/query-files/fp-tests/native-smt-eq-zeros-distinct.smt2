; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; SMT's = on the FloatingPoint sort separates the zeros -- the domain has
; two of them, and they are different values even though fp.eq identifies
; them. So x = -0 forces y to -0 as well, contradicting fp.isPositive y, and
; this formula is unsatisfiable. The native encoding (BBeqFP) gets this for
; free from bit equality; copy fp.eq's both-zero disjunct into the SMT
; equality by mistake and x = -0, y = +0 makes it sat.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= x y))
(assert (fp.isZero x))
(assert (fp.isNegative x))
(assert (fp.isPositive y))
(check-sat)
(exit)
