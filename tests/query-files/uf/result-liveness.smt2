; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
(set-logic QF_UFBV)
(declare-fun p ((_ BitVec 8)) Bool)
(declare-fun f (Bool) (_ BitVec 8))
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(declare-fun r ((_ BitVec 8)) Bool)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= x y))
; p's Boolean results and g's BV results occur only as nested UF actuals.
; Both must be totalized before the first checker candidate.
(assert (distinct (f (p x)) (f (p y))))
(assert (r (g x)))
(assert (not (r (g y))))
(check-sat)
