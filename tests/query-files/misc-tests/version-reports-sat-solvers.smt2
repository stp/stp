; RUN: %solver --version %s | %OutputCheck %s
;
; --version names the SAT backends compiled into the binary and the version
; each linked library reports at run time. Which SAT library is behind a
; build is not otherwise visible from outside it, yet it decides both the
; answers and the timings, so a build linking a different solver than
; intended is a silent and expensive mistake to make.
;
; Only the label is checked: the list itself depends on the configure-time
; options, and a build with a single backend is as valid as one with four.
;
; CHECK: ^STP SAT solvers
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x (_ bv1 4)))
(check-sat)
(exit)
