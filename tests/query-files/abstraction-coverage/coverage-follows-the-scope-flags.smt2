; ... and that the three scope flags reach the blaster. The same query with
; if-then-else, addition and comparison switched off: each is still counted
; as a candidate and none is taken, while the multiplication is untouched.
; The candidate counts staying put is the point -- they say what was on
; offer, not what was accepted.
; RUN: %solver -t --bv-term-abstraction=1 --bv-term-abstraction-ite=0 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 128))
(declare-fun b () (_ BitVec 128))
(declare-fun c () (_ BitVec 128))
(assert (= (bvmul a b) c))
(assert (bvult a b))
(assert (= (bvadd a b) (bvnot c)))
(assert (= (ite (bvult b c) a b) c))
; CHECK: Abstraction coverage \(candidates -> abstracted\): eq=2->0 compare=2->0 ite=1->0 plus=1->0 mult=1->1 divmod=0->0
(check-sat)
(exit)
