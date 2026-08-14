; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Read congruence propagates across a chain of float-element array
; equalities: a non-NaN cell cannot fp.eq-differ from itself two
; equalities away.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun b () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun c () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(assert (= a b))
(assert (= b c))
(assert (not (fp.eq (select a #x3) (select c #x3))))
(assert (not (fp.isNaN (select a #x3))))
(check-sat)
