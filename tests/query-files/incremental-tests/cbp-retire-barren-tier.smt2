; The cross-level constant-bit pass retires itself on evidence of futility,
; and picks between two leashes: a session whose engine has never DERIVED a
; fixing gets a short one, while a session with fixings but no adoption yet
; gets a long one, because adoption can legitimately arrive late.
;
; Every fed level is asserted, so its conjunction and each of its top-level
; conjuncts are fixed to TRUE by assumption alone -- a derivation of nothing.
; Counting those made the "never derived a fixing" flag true after the first
; array-free feed, so the short leash was unreachable for exactly the
; pop-per-query sessions it was measured on, and they served out the long one
; instead: this file retired after 64 divergences rather than 8.
;
; Nothing here is derivable: the levels constrain b and c only through a
; disjunction, and no bit of any symbol is ever fixed.
; RUN: %solver --incremental -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 -s %s 2>&1 | %OutputCheck %s
; CHECK: cbp retired for the session \(8 adoption-free stack divergences\)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(assert (bvult a b))
(push 1)
(assert (or (bvult b c) (bvugt c #x01)))
(check-sat)
(pop 1)
(push 1)
(assert (or (bvult b c) (bvugt c #x02)))
(check-sat)
(pop 1)
(push 1)
(assert (or (bvult b c) (bvugt c #x03)))
(check-sat)
(pop 1)
(push 1)
(assert (or (bvult b c) (bvugt c #x04)))
(check-sat)
(pop 1)
(push 1)
(assert (or (bvult b c) (bvugt c #x05)))
(check-sat)
(pop 1)
(push 1)
(assert (or (bvult b c) (bvugt c #x06)))
(check-sat)
(pop 1)
(push 1)
(assert (or (bvult b c) (bvugt c #x07)))
(check-sat)
(pop 1)
(push 1)
(assert (or (bvult b c) (bvugt c #x08)))
(check-sat)
(pop 1)
(push 1)
(assert (or (bvult b c) (bvugt c #x09)))
(check-sat)
(pop 1)
(push 1)
(assert (or (bvult b c) (bvugt c #x0a)))
(check-sat)
(exit)
