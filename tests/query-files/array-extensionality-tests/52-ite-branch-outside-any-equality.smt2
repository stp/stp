; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; An array reachable only as the far branch of an array if-then-else
; sitting above an equality operand.
;
; The only equality here is (distinct _x2 _x4), but the active checker
; owns the complete root, including _x0 in the other branch. Earlier
; equality-operand-only protection never saw _x0; preprocessing could
; therefore delete one of its reads before later graph closure reached it.
;
; Nothing at construction time could have anticipated it: the
; if-then-else is above the operand, not inside it, and here it cannot
; even exist when the equality is built, since the equality is its own
; condition. Ownership is therefore snapshotted where the whole formula
; and active registry are known and no pass has yet acted on the answer.
;
; Found by a murxla campaign against the floating-point branch; delta
; minimization removed the floating point entirely, so it belongs here.
(declare-fun _x0 () (Array (_ BitVec 20) (_ BitVec 20)))
(declare-fun _x2 () (Array (_ BitVec 20) (_ BitVec 20)))
(declare-fun _x3 () (_ BitVec 20))
(declare-fun _x4 () (Array (_ BitVec 20) (_ BitVec 20)))
(assert (bvuge _x3 (select (ite (distinct _x2 _x4) _x4 _x0) _x3)))
(check-sat)
