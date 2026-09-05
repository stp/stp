; RUN: %solver %s | %OutputCheck %s
;
; define-sort declarations follow the same scopes as other declarations.
; pop, reset and (with :global-declarations false) reset-assertions discard
; them at the levels those commands remove.
(set-logic QF_FP)

(push 1)
(define-sort Scoped () (_ FloatingPoint 3 5))
(declare-const inner Scoped)
(assert (fp.isNormal inner))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)

; The name from the popped frame is available again, at a different format.
(define-sort Scoped () (_ FloatingPoint 5 11))
(define-sort Kept () (_ FloatingPoint 8 24))
(push 1)
(define-sort Dropped () (_ FloatingPoint 4 4))
(declare-const temporary Dropped)
(assert (fp.isNormal temporary))
(reset-assertions)

; Both base and pushed aliases were discarded, so all names are reusable at
; different formats.
(define-sort Scoped () (_ FloatingPoint 8 24))
(define-sort Kept () (_ FloatingPoint 4 5))
(define-sort Dropped () (_ FloatingPoint 6 8))
(declare-const base_value Scoped)
(declare-const kept_value Kept)
(declare-const replacement Dropped)
(assert (and (fp.isNormal base_value)
             (fp.isNormal kept_value)
             (fp.isNormal replacement)))
; CHECK-NEXT: ^sat
(check-sat)

; Full reset does so as well.
(reset)
(set-logic QF_FP)
(define-sort Scoped () (_ FloatingPoint 8 24))
(declare-const after_reset Scoped)
(assert (fp.isNormal after_reset))
; CHECK-NEXT: ^sat
(check-sat)
