; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^unsat
; A solve with an array if-then-else and no array equality, followed by
; a solve whose array equality is over an if-then-else built after it.
; The first uses the legacy array path and must leave the second undisturbed;
; the active second solve preserves the if-then-else and handles it with the
; checker's direct T-up/T-down rules.
;
; Historically this exposed the incremental hazard of deciding ITE
; replacement at construction. The undoing left the node factory bypassed on
; the way out --
; it had to, since preprocessing rebuilds array if-then-elses as it
; simplifies -- and the scope guard that put the factory back was armed
; only when the procedure had run, which is exactly when the undoing
; does nothing. One inactive solve therefore disabled replacement for
; the rest of the session, and the second query died on
;   Assertion `coneITEs.empty()' failed
; or, with assertions off,
;   TransformArrayRead: an array-valued if-then-else survived inside the
;   array-equality cone
;
; The second query is unsat by cases on q: c is a if q and b otherwise,
; and both are asserted to differ from c at i.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun c () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun i () (_ BitVec 2))
(assert (= (select (ite p a b) #b00) #b00))
(check-sat)
(assert (= (ite q a b) c))
(assert (distinct (select a i) (select c i)))
(assert (distinct (select b i) (select c i)))
(check-sat)
