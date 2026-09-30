; Bool-valued selects are terms in macro bodies, lets, qualified identifiers,
; annotations and Boolean connectives, as well as array operands.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=off %s | %OutputCheck %s
(set-logic ALL)
(define-sort Flags () (Array Bool Bool))
(define-fun update ((a Flags) (i Bool) (v Bool)) Flags (store a i v))
(define-fun read ((a Flags) (i Bool)) Bool (select a i))
(declare-const a Flags)
(declare-const p Bool)
(declare-fun f (Bool) Bool)
(assert (read a false))
(assert (not ((as select Bool) a true)))
(assert (f (select a false)))
(assert (= (f true) (select a false)))
(assert (= (ite p (select a false) (select a true)) p))
(assert (let ((v (select a p)))
          (and (= v (not p))
               (select (update a v (or p (not p))) v))))
(assert (= (! (select a false) :named read_false) true))
; CHECK-NEXT: ^sat$
(check-sat)
(push 1)
(assert (distinct read_false true))
; CHECK-NEXT: ^unsat$
(check-sat)
(pop 1)
(assert (distinct (select a false) (select a true) p))
; CHECK-NEXT: ^unsat$
(check-sat)
