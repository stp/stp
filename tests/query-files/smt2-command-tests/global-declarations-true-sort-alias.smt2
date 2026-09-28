; Sort aliases are definitions too, so define-sort obeys the option alongside
; declare-fun and define-fun: the alias made inside the pushed level is still a
; usable sort after the pop. define-sort-alias-scope covers the false side.
; RUN: %solver %s | %OutputCheck %s
(set-option :global-declarations true)
(set-logic QF_FP)
(push 1)
(define-sort F32 () (_ FloatingPoint 8 24))
(pop 1)
(declare-const f F32)
(assert (fp.isNormal f))
; CHECK: ^sat$
(check-sat)
