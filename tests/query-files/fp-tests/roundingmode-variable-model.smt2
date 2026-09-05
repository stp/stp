; RUN: %solver %s | %OutputCheck %s
;
; The value of a RoundingMode symbol prints by mode name -- a legal term of
; the sort -- in both get-model and get-value, not as the raw 5-bit carrier
; (which used to leak out, e.g. #b01000). The declaration's one-hot
; constraint guarantees the value always names a mode, even for a symbol no
; user assertion mentions.
(set-logic QF_FP)
(set-option :produce-models true)
(declare-const r RoundingMode)
(declare-fun unused () RoundingMode)
(assert (= r roundTowardZero))
; CHECK: ^sat
(check-sat)
; (CHECK-L: these patterns hold regex metacharacters -- | -- so the plain
; CHECK form would match vacuously.)
; CHECK-L: define-fun |r| () RoundingMode RTZ
(get-model)
; CHECK-L: ( |r| RTZ )
(get-value (r))
