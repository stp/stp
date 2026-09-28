; RUN: %solver %s | %OutputCheck %s
;
; The extremes the unconstrained-fp.gt rule must not mis-eliminate: nothing
; exceeds +oo, nothing lies below -oo, and nothing compares to NaN. Each
; query is unsatisfiable, and each stresses one guard of the rule (the rule
; declines these and leaves them to the blasted circuit, which must then
; agree). Queries are separate so one wrong answer cannot mask another.
;
; CHECK: ^unsat
(set-logic QF_FP)
(push 1)
(declare-fun a () (_ FloatingPoint 8 24))
(assert (fp.gt a (_ +oo 8 24)))
(check-sat)
(pop 1)
; CHECK: ^unsat
(push 1)
(declare-fun b () (_ FloatingPoint 8 24))
(assert (fp.gt b (_ NaN 8 24)))
(check-sat)
(pop 1)
; CHECK: ^unsat
(push 1)
(declare-fun c () (_ FloatingPoint 8 24))
(assert (fp.gt (_ -oo 8 24) c))
(check-sat)
(pop 1)
; CHECK: ^unsat
(push 1)
(declare-fun d () (_ FloatingPoint 8 24))
(assert (fp.gt (_ NaN 8 24) d))
(check-sat)
(pop 1)
(exit)
