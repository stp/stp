; The counters exist so that what the abstraction actually took can be read
; off a run. This pins the line they print: one query holding a wide
; comparison, if-then-else, addition and multiplication, each of which the
; abstraction takes at this width, and two equalities which it does not --
; --bv-eq-abstraction is a separate switch and is off here.
; RUN: %solver -t --bv-term-abstraction=1 %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 128))
(declare-fun b () (_ BitVec 128))
(declare-fun c () (_ BitVec 128))
(assert (= (bvmul a b) c))
(assert (bvult a b))
(assert (= (bvadd a b) (bvnot c)))
(assert (= (ite (bvult b c) a b) c))
; CHECK: Abstraction coverage \(candidates -> abstracted\): eq=2->0 compare=2->2 ite=1->1 plus=1->1 mult=1->1 divmod=0->0
(check-sat)
(exit)
