; Native-domain fact collection is enabled by default and remains independent
; of the domain rewrite prepass and known-sign arithmetic specialization. The
; explicit false value remains available as an opt-out. Disable the independent
; zero-fact, derived-bound, and selector defaults in both runs so the negative
; checks isolate this flag.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --fp-domain-derived-bounds=0 --fp-domain-extremal-selectors=0 --fp-domain-sound-zero-facts=0 -s %s 2>&1 | %OutputCheck --check-prefix=DEFAULT %s
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --fp-domain-derived-bounds=0 --fp-domain-extremal-selectors=0 --fp-domain-sound-zero-facts=0 --bb.fp-native-domain=false -s %s 2>&1 | %OutputCheck --check-prefix=OFF %s
;
; DEFAULT: FP native domain finite terms: [1-9][0-9]*
; DEFAULT: FP native domain classifications: [1-9][0-9]*
; DEFAULT: FP native domain known-positive add paths: 0
; DEFAULT-NOT: FpDomainSimplify:
; DEFAULT: ^unsat
;
; OFF-NOT: FP native domain
; OFF-NOT: FpDomainSimplify:
; OFF: ^unsat
;
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 3 5))

(define-fun one () (_ FloatingPoint 3 5) (fp #b0 #b011 #b0000))
(define-fun two () (_ FloatingPoint 3 5) (fp #b0 #b100 #b0000))

(assert (and (fp.leq one x) (fp.leq x two)))
(assert (fp.isNaN x))
(check-sat)
(exit)
