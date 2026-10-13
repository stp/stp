; A label is defined when its annotation is reduced, before the enclosing
; term is built, so constant folding of that term cannot lose it.
; RUN: %solver %s | %OutputCheck %s
(set-option :produce-models true)
(set-option :produce-assignments true)
(set-option :produce-unsat-cores true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y Bool)
(assert (or true (! y :named under-or)))
(assert (= (ite true #x01 (! x :named dead-branch)) #x01))
(assert (= (and false (! (= x #x07) :named under-and)) false))
(assert (not under-or))
(assert (= dead-branch #x07))
(assert under-and)
; CHECK: ^sat$
(check-sat)
; CHECK-L: (under-or false)
; CHECK-L: (y false)
; CHECK-L: (dead-branch #x07)
; CHECK-L: (x #x07)
; CHECK-L: (under-and true)
(get-value (under-or y dead-branch x under-and))
; CHECK-L: ((|under-and| true) (|under-or| false))
(get-assignment)
(push 1)
; A label under a folded conjunct still labels its assertion for the core,
; and an assertion folded to true contributes nothing.
(assert (! (or true y) :named tautology))
(assert (! (and true (! (= x #x07) :named inner)) :named outer))
(assert (! (not inner) :named negated))
; CHECK: ^unsat$
(check-sat)
; CHECK-L: (|outer| |negated|)
(get-unsat-core)
(pop 1)
