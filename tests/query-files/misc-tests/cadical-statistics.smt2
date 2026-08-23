; REQUIRES: cadical-inprobing
; RUN: %solver --cadical -s %s 2>&1 | %OutputCheck %s
; CHECK: CaDiCaL conflicts: {{[0-9]+}}
; CHECK: CaDiCaL decisions: {{[0-9]+}}
; CHECK: CaDiCaL search propagations: {{[0-9]+}}
; CHECK: CaDiCaL search ticks: {{[0-9]+}}
; CHECK-NOT: print stats not yet implemented
; CHECK: ^sat
; Keep enough coupled structure to reach the SAT backend instead of being
; discharged by unconstrained-variable elimination.
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(define-fun one () (_ FloatingPoint 8 24)
  ((_ to_fp 8 24) #x3f800000))
(assert (fp.lt one x))
(assert (fp.lt one y))
(assert (not (fp.isInfinite x)))
(assert (not (fp.isInfinite y)))
(assert (fp.gt (fp.mul RNE x y) x))
(assert (fp.gt (fp.mul RNE x y) y))
(check-sat)
