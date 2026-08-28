; The counters exist so that what the abstraction actually took can be read
; off a run. This pins the line they print: one query holding a wide
; comparison, if-then-else, addition and multiplication, each of which the
; abstraction takes at this width, and two equalities which it does not --
; --bv-eq-abstraction is a separate switch and is off here.
; RUN: %solver -t --bv-term-abstraction=1 %s 2>&1 | %OutputCheck %s
; RUN: %solver -t --exit-after-CNF --bv-term-abstraction=1 %s 2>&1 | %OutputCheck %s --check-prefix=EARLY
(set-logic QF_BV)
(declare-fun a () (_ BitVec 128))
(declare-fun b () (_ BitVec 128))
(declare-fun c () (_ BitVec 128))
(assert (= (bvmul a b) c))
(assert (bvult a b))
(assert (= (bvadd a b) (bvnot c)))
(assert (= (ite (bvult b c) a b) c))
; CHECK: Abstraction coverage \(candidates -> abstracted\): eq=2->0 compare=2->2 ite=1->1 plus=1->1 mult=1->1 divmod=0->0
; CHECK: Abstraction schemas by group: base=[0-9]+ udiv15=0 udiv-observed=0 udiv-tail=0 urem=[0-9]+ quotient-one-quot=0 quotient-one-rem=0 quotient-thresholds=0 divisor-magnitude=0 divrem-full=0 mul8=0 mul-ref3=[0-9]+ mul-tail=0 add=0 low-prefix=0
; EARLY: Abstraction coverage \(candidates -> abstracted\): eq=2->0 compare=2->2 ite=1->1 plus=1->1 mult=1->1 divmod=0->0
; EARLY: Abstraction refinement: rounds=0 blocking=0 schema=0 exact=0 exact-mult=0 exact-divmod=0
; EARLY-NOT: Abstraction circuit cost:
(check-sat)
(exit)
