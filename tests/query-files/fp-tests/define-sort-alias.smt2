; RUN: %solver %s | %OutputCheck %s
;
; define-sort aliases live in a real table now: usable in declare-fun and
; declare-const sort position, at any format. (They used to be interned as
; TERM symbols, so the alias name doubled as a free variable.)
(set-logic QF_FP)
(define-sort MyFloat () (_ FloatingPoint 8 24))
(define-sort Tiny () (_ FloatingPoint 3 5))
(declare-fun x () MyFloat)
(declare-const y MyFloat)
(declare-const t Tiny)
(assert (fp.lt x y))
(assert (fp.isNormal t))
; CHECK: ^sat
(check-sat)
