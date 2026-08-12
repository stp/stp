; The automatic engagement threshold names the real solve whose work first
; reaches the persistent driver. Five delays the driver through four changing
; stacks; zero keeps every solve on the batch path. Explicit --incremental
; remains an unconditional first-solve override.
; RUN: %solver -s --incremental-auto-engage-at 5 %s 2>&1 | %OutputCheck --check-prefix=FIVE %s
; RUN: %solver -s --incremental-auto-engage-at 0 %s 2>&1 | %OutputCheck --check-prefix=NEVER %s
; RUN: %solver -s --incremental-auto-engage-at 0 --incremental %s 2>&1 | %OutputCheck --check-prefix=FORCED %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (bvult x #x80))

(push 1)
(assert (bvult x #x70))
; FIVE-NOT: Incremental: encoded
; FIVE: ^sat
; NEVER-NOT: Incremental: encoded
; NEVER: ^sat
; FORCED: Incremental: encoded
; FORCED: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (bvult x #x60))
; FIVE-NOT: Incremental: encoded
; FIVE: ^sat
; NEVER-NOT: Incremental: encoded
; NEVER: ^sat
; FORCED: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (bvult x #x50))
; FIVE-NOT: Incremental: encoded
; FIVE: ^sat
; NEVER-NOT: Incremental: encoded
; NEVER: ^sat
; FORCED: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (bvult x #x40))
; FIVE-NOT: Incremental: encoded
; FIVE: ^sat
; NEVER-NOT: Incremental: encoded
; NEVER: ^sat
; FORCED: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (bvuge x #x80))
; FIVE: Incremental: encoded
; FIVE: ^unsat
; NEVER-NOT: Incremental: encoded
; NEVER: ^unsat
; FORCED: ^unsat
(check-sat)
(pop 1)
; NEVER-NOT: Incremental: encoded
(exit)
