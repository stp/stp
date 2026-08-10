; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; The other half of SMT-LIB 2's reserved namespace. Pure bit-vector input:
; the rule is not a floating-point one, it is what makes every symbol STP
; mints for itself -- CreateFreshVariable's, the array transformer's, the
; unconstrained-variable eliminator's -- safe to assume unique.
;
; CHECK: reserved for solver use
(set-logic QF_BV)
(declare-fun |.hidden| () (_ BitVec 8))
(assert (= |.hidden| #x01))
(check-sat)
