; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
; Bool and BV define-fun formals both retain SourceSort through substitution
; into a durable mixed-signature application.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8) Bool) (_ BitVec 8))
(define-fun h ((x (_ BitVec 8)) (b Bool)) (_ BitVec 8) (f x b))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const b Bool)
(declare-const c Bool)
(assert (= x y))
(assert (= b c))
(assert (distinct (h x b) (h y c)))
(check-sat)
