; A repaired first query must not mark a discarded release as asserted.
; Otherwise the second query accepts the unconstrained surrogate for x/x.
; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true --fp-abstraction-tiers=0 --fp-abstraction-shape=false --fp-abstraction-relational=false --fp-abstraction-values=0 --fp-abstraction-repair=true %s | %OutputCheck %s
; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true --fp-abstraction-tiers=0 --fp-abstraction-shape=false --fp-abstraction-relational=false --fp-abstraction-values=0 --fp-abstraction-repair=false %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 5 11))
(define-fun t () (_ FloatingPoint 5 11) (fp.div RNE x x))
(assert (fp.isNormal x))
(assert (fp.isNormal t))
(check-sat)
(push 1)
(assert (not (= t ((_ to_fp 5 11) #x3c00))))
(check-sat)
(pop 1)
(check-sat)
(assert (not (= t ((_ to_fp 5 11) #x3c00))))
(check-sat)
(exit)
