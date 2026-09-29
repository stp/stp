; RUN: not %solver --exit-after-CNF --stop-after-cnf %s 2>&1 | %OutputCheck %s
; RUN: not %solver --stop-after-cnf --exit-after-CNF %s 2>&1 | %OutputCheck %s
;
; --exit-after-CNF ends the run at the first CNF, --stop-after-cnf stops that
; check and goes on: given both, the run used to go on and answer every
; check-sat after the first, as if --exit-after-CNF had not been given.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvmul x y) #x0000ec4b))
(check-sat)
(check-sat)
; CHECK: --exit-after-CNF excludes --stop-after-cnf
; CHECK-NOT: sat
