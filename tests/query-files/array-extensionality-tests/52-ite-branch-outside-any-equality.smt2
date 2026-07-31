; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; An array reachable only as the far branch of an array if-then-else
; sitting above an equality operand.
;
; The only equality here is (distinct _x2 _x4), so the cone seeds at
; _x2 and _x4. It closes upward onto the if-then-else that has _x4 as a
; branch, and then downward into the other branch -- reaching _x0,
; which no equality mentions. possibleConeSymbols is collected from the
; operands, so it had never seen _x0, its reads were not protected from
; the read-equals-constant substitution, and the containment guard
; aborted the solve with exit 255.
;
; Nothing at construction time could have anticipated it: the
; if-then-else is above the operand, not inside it, and here it cannot
; even exist when the equality is built, since the equality is its own
; condition. The closure is therefore run once more where the whole
; formula and the whole registry are both known and no pass has yet
; acted on the answer.
;
; Found by a murxla campaign against the floating-point branch; delta
; minimization removed the floating point entirely, so it belongs here.
(declare-fun _x0 () (Array (_ BitVec 20) (_ BitVec 20)))
(declare-fun _x2 () (Array (_ BitVec 20) (_ BitVec 20)))
(declare-fun _x3 () (_ BitVec 20))
(declare-fun _x4 () (Array (_ BitVec 20) (_ BitVec 20)))
(assert (bvuge _x3 (select (ite (distinct _x2 _x4) _x4 _x0) _x3)))
(check-sat)
