; RUN: not %solver --threads 0 %s 2>&1 | %OutputCheck --check-prefix=ZERO %s
; RUN: not %solver --threads -1 %s 2>&1 | %OutputCheck --check-prefix=NEGATIVE %s
; RUN: not %solver --threads 1025 %s 2>&1 | %OutputCheck --check-prefix=HUGE %s
;
; CryptoMiniSat takes a thread count from 1: 0 made it throw part way
; through the first check, and a negative count became a huge unsigned one
; whose threads never finished starting, beyond max-time and interrupts.
; The option refuses them before anything runs.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= x #x03))
(check-sat)
; ZERO: --threads must be 1 or greater
; ZERO-NOT: sat
; NEGATIVE: --threads must be 1 or greater
; NEGATIVE-NOT: sat
; HUGE: --threads must be at most 1024
; HUGE-NOT: sat
