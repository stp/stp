; RUN: %solver %s | %OutputCheck %s
;
; A function over Reals that no assertion applies still gets a definition,
; the codomain's zero. Seeding it with a packed zero used to abort get-model:
; a Real has no packed width.
(set-logic QF_UFLRA)
(set-option :produce-models true)
(declare-fun f (Real) Real)
(declare-fun p (Real Bool) Bool)
(declare-fun x () Real)
(assert (> x 1.5))
(check-sat)
(get-model)
(get-value ((f x) (p x true)))
; CHECK: ^sat
; CHECK: ^\(define-fun \|f\| \(\(x0 Real\)\) Real$
; CHECK-NEXT: ^  0\)$
; CHECK: ^\(define-fun \|p\| \(\(x0 Real\) \(x1 Bool\)\) Bool$
; CHECK-NEXT: ^  false\)$
; CHECK: \(\(\|f\| \|x\|\) 0\)
; CHECK: \(\|p\| \|x\| true\) false
