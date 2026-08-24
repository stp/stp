; RUN: %solver -s %s 2>&1 | %OutputCheck --check-prefix=DEFAULT %s
; RUN: %solver --fp-domain-derived-bounds=0 --fp-domain-sound-zero-facts=0 -s %s 2>&1 | %OutputCheck --check-prefix=DISABLED %s
; RUN: %solver --fp-domain-derived-bounds=0 --fp-domain-sound-zero-facts=1 -s %s 2>&1 | %OutputCheck --check-prefix=ZERO-ONLY %s
; RUN: %solver --fp-domain-derived-bounds=0 --fp-domain-simplify=1 --fp-domain-sound-zero-facts=1 -s %s 2>&1 | %OutputCheck --check-prefix=COMBINED %s
;
; DEFAULT: FpDomainSimplify: 3 boxed symbols, 0 interval-true, 0 interval-false, 0 classifier-false, 0 diff-zero-eq, 0 nonnegative-zero-sum, 2 sound-zero-rows, 3 sound-zero-facts
; DEFAULT: sat
;
; DISABLED-NOT: FpDomainSimplify:
; DISABLED: sat
;
; ZERO-ONLY: FpDomainSimplify: 3 boxed symbols, 0 interval-true, 0 interval-false, 0 classifier-false, 0 diff-zero-eq, 0 nonnegative-zero-sum, 2 sound-zero-rows, 3 sound-zero-facts
; ZERO-ONLY: sat
;
; COMBINED: FpDomainSimplify: 3 boxed symbols, 0 interval-true, 0 interval-false, 0 classifier-false, 1 diff-zero-eq, 1 nonnegative-zero-sum, 2 sound-zero-rows, 3 sound-zero-facts
; COMBINED: sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))
(assert (and (fp.leq (_ +zero 8 24) x)
             (fp.leq x (fp #b0 #b10000001 #b00000000000000000000000))
             (fp.leq (_ +zero 8 24) y)
             (fp.leq y (fp #b0 #b10000001 #b00000000000000000000000))
             (fp.leq (_ +zero 8 24) z)
             (fp.leq z (fp #b0 #b10000001 #b00000000000000000000000))
             (fp.eq (fp.add RNE x y) (_ +zero 8 24))
             (fp.eq (fp.add RNE z (fp.neg y)) (_ +zero 8 24))))
(check-sat)
