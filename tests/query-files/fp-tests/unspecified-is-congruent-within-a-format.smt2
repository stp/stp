; RUN: %solver %s | %OutputCheck %s
;
; The other half of the totalisation contract, and the reason the unspecified
; results go through a shared array at all: within one sort the result is a
; *function* of the operands, so two occurrences of the same application
; answer the same way. Demanding both zeros back from one of them is
; unsatisfiable.
;
; Pinned alongside unspecified-per-format-not-per-width.smt2: that test wants
; two formats kept apart, and the cheap way to pass it -- a fresh array per
; occurrence -- would break this one.
; CHECK: ^unsat
(set-logic QF_FP)
(assert (fp.isNegative (fp.min (_ +zero 8 24) (_ -zero 8 24))))
(assert (fp.isPositive (fp.min (_ +zero 8 24) (_ -zero 8 24))))
(check-sat)
