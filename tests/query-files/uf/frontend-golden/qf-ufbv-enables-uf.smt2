; QF_UFBV selects the UF frontend by itself. In particular, it is not accepted
; merely as an inert label: a non-nullary application is decided too.
;
; RUN: %solver %s 2>&1 | %OutputCheck %s
; CHECK-NOT: Wrong input logic
; CHECK: ^unsat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(assert (distinct (f #x0) (f #x0)))
(check-sat)
