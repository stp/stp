; REQUIRES: minisat
; RUN: %solver --minisat -s %s 2>&1 | %OutputCheck --check-prefix=STATS %s
; RUN: %solver --simplifying-minisat -s %s 2>&1 | %OutputCheck --check-prefix=STATS %s
; STATS: MiniSat starts: {{[0-9]+}}
; STATS: MiniSat conflicts: {{[0-9]+}}
; STATS: MiniSat decisions: {{[0-9]+}}
; STATS: MiniSat propagations: {{[0-9]+}}
; STATS: MiniSat variables: {{[0-9]+}}
; STATS: MiniSat active original clauses: {{[0-9]+}}
; STATS: MiniSat active original literals: {{[0-9]+}}
; STATS: MiniSat active learnt clauses: {{[0-9]+}}
; STATS: MiniSat active learnt literals: {{[0-9]+}}
; STATS: MiniSat learnt literals before minimization: {{[0-9]+}}
; STATS: MiniSat learnt literals after minimization: {{[0-9]+}}
; STATS: ^sat
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
