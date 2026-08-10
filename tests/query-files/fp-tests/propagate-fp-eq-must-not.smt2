; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
;
; fp.eq must NEVER be propagated as a substitution: it identifies +0 with
; -0, which fp.isNegative distinguishes. Here x = -0 is the only model --
; fp.eq(-0, +0) is true and isNegative(-0) is true. If fp.eq ever feeds
; the substitution map, x becomes +0 and this flips to unsat. (SMT = is
; the propagatable equality; fp.eq is IEEE equality on the quotient.)
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp #b0 #b00000000 #b00000000000000000000000)))
(assert (fp.isNegative x))
(check-sat)
(exit)
