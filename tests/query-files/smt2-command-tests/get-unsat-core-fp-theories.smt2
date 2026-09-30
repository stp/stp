; Selectors survive floating-point totalisation, including the value equality
; and witness constraints of arrays whose sorts quotient their bit patterns.
; RUN: %solver --uf-ackermann=off --array-ackermann-budget=0 %s | %OutputCheck %s
; RUN: %solver --incremental-core-only --uf-ackermann=off --array-ackermann-budget=0 %s | %OutputCheck %s
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-const r Bool)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(declare-fun f ((_ FloatingPoint 5 11)) (_ BitVec 8))
(assert (! r :named irrelevant))
(assert (! (= x y) :named left))
(assert (! (distinct (f x) (f y)) :named right))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|left\| \|right\|\)$
(get-unsat-core)

(reset)
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-const r Bool)
(declare-const a (Array (_ FloatingPoint 5 11) (_ FloatingPoint 5 11)))
(declare-const b (Array (_ FloatingPoint 5 11) (_ FloatingPoint 5 11)))
(declare-const x (_ FloatingPoint 5 11))
(assert (! r :named irrelevant))
(assert (! (= a b) :named left))
(assert (! (distinct (select a x) (select b x)) :named right))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|left\| \|right\|\)$
(get-unsat-core)
