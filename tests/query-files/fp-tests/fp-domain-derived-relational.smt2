; A symbol/expression relation supplies a finite endpoint for r. The
; experiment is decision-only: it keeps both source relations and uses the
; resulting [0,4] box only to refute the separate objective.
;
; RUN: %solver --fp-domain-sound-zero-facts=0 --fp-domain-derived-bounds=1 --fp-domain-extremal-selectors=0 -s %s 2>&1 | %OutputCheck --check-prefix=DERIVED %s
; RUN: %solver --fp-domain-sound-zero-facts=0 -s %s 2>&1 | %OutputCheck --check-prefix=DEFAULT %s
; RUN: %solver --fp-domain-sound-zero-facts=0 --fp-domain-derived-bounds=0 --fp-domain-extremal-selectors=0 %s | %OutputCheck --check-prefix=BASE %s
; DERIVED: FpDomainSimplify: 2 boxed symbols, 0 interval-true, 1 interval-false, .* 2 derived-relations, 2 derived-bounds
; DERIVED: unsat
; DEFAULT: FpDomainSimplify: 2 boxed symbols, 0 interval-true, 1 interval-false, .* 2 derived-relations, 2 derived-bounds
; DEFAULT: unsat
; BASE: unsat

(set-logic QF_FP)
(declare-fun s () (_ FloatingPoint 8 24))
(declare-fun r () (_ FloatingPoint 8 24))
(define-fun one () (_ FloatingPoint 8 24)
  (fp #b0 #x7f #b00000000000000000000000))
(define-fun four () (_ FloatingPoint 8 24)
  (fp #b0 #x81 #b00000000000000000000000))
(define-fun six () (_ FloatingPoint 8 24)
  (fp #b0 #x81 #b10000000000000000000000))

(assert (and (fp.leq (_ +zero 8 24) s)
             (fp.leq s one)
             (fp.leq r (fp.mul RNE four s))
             (fp.leq s r)))
(assert (fp.gt (fp.add RNE r one) six))
(check-sat)
(exit)
