; RUN: %solver --incremental --fp-abstraction=true --fp-abstraction-incremental=true --fp-abstraction-ops=fma,mul,add --fp-abstraction-repair=false %s | %OutputCheck %s
; RUN: %solver --incremental --incremental-core-only --fp-abstraction=true --fp-abstraction-incremental=true --fp-abstraction-ops=fma,mul,add --fp-abstraction-repair=false %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
;
; Discover the product after the piece that introduced the FMA is popped.
; Its cross-rule closure must carry definitions, while allowing the old
; assertion isNormal(t) to retract: at (1,1,-1), q=1 and t=0.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 5 11))
(declare-fun y () (_ FloatingPoint 5 11))
(declare-fun z () (_ FloatingPoint 5 11))
(define-fun t () (_ FloatingPoint 5 11) (fp.fma RNE x y z))
(define-fun q () (_ FloatingPoint 5 11) (fp.mul RNE y x))
(push 1)
(assert (fp.isNormal t))
(check-sat)
(pop 1)
(push 1)
(assert (fp.isNormal q))
(push 1)
(assert (= x ((_ to_fp 5 11) #x3c00)))
(assert (= y ((_ to_fp 5 11) #x3c00)))
(assert (= z ((_ to_fp 5 11) #xbc00)))
(check-sat)
(push 1)
(assert (not (fp.isZero t)))
(check-sat)
(pop 1)
(push 1)
(assert (not (= t (fp.add RNE x z))))
(check-sat)
(pop 2)
(assert (fp.isNormal t))
(check-sat)
(exit)
