; The first objective is the exact maximum of 4*s-2*t and uniquely requires
; s=1, t=semantic-zero. Structural t=-0 must remain satisfiable: the emitted
; zero fact is IEEE equality/isZero, never packed equality to +0. The second
; objective has an interior value. One endpoint is necessary, but the partial
; facts are not sufficient, so that equality must not be replaced. The
; matching ordered threshold is equivalent to u=1 and is safely replaced:
; exact extrema are the primary case, not an artificial syntactic condition.
; The structural {+0,1} disjunction for w is deliberately not treated as a
; semantic selector domain.
;
; RUN: %solver --fp-domain-sound-zero-facts=0 --fp-domain-extremal-selectors=1 -s %s 2>&1 | %OutputCheck --check-prefix=SELECTOR %s
; RUN: %solver --fp-domain-sound-zero-facts=0 %s | %OutputCheck --check-prefix=BASE %s
; SELECTOR: 4 extremal-selector-domains, 3 extremal-selector-predicates, 3 extremal-selector-facts, 2 extremal-selector-rewrites
; SELECTOR: sat
; BASE: sat

(set-logic QF_FP)
(declare-fun s () (_ FloatingPoint 8 24))
(declare-fun t () (_ FloatingPoint 8 24))
(declare-fun u () (_ FloatingPoint 8 24))
(declare-fun v () (_ FloatingPoint 8 24))
(declare-fun w () (_ FloatingPoint 8 24))
(define-fun one () (_ FloatingPoint 8 24)
  (fp #b0 #x7f #b00000000000000000000000))
(define-fun two () (_ FloatingPoint 8 24)
  (fp #b0 #x80 #b00000000000000000000000))
(define-fun minusTwo () (_ FloatingPoint 8 24)
  (fp #b1 #x80 #b00000000000000000000000))
(define-fun four () (_ FloatingPoint 8 24)
  (fp #b0 #x81 #b00000000000000000000000))

(assert (and
  (or (fp.eq s (_ -zero 8 24)) (fp.eq s one))
  (or (fp.eq t (_ +zero 8 24)) (fp.eq t one))
  (or (fp.eq u (_ +zero 8 24)) (fp.eq u one))
  (or (fp.eq v (_ +zero 8 24)) (fp.eq v one))
  (or (= w (_ +zero 8 24)) (= w one))))

(define-fun objective ((a (_ FloatingPoint 8 24))
                       (b (_ FloatingPoint 8 24)))
  (_ FloatingPoint 8 24)
  (fp.add RNE (fp.mul RNE four a) (fp.mul RNE minusTwo b)))

(assert (fp.eq (objective s t) four))
(assert (= t (_ -zero 8 24)))
(assert (fp.eq (objective u v) two))
(assert (fp.geq (objective u v) two))
(check-sat)
(exit)
