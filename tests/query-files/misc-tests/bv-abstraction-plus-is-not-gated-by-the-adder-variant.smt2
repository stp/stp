; Which adder the bit-blaster would have used does not decide whether an
; addition is abstracted.
;
; --bb.add-v2 chooses between the two lowerings BBTerm has for BVPLUS:
; pairwise BBPlus2 accumulation, and the addition network. The abstraction
; reaches neither. It returns before both of them, and the exact encoding it
; escalates to is spliced in at CNF level through BVExactEncoder rather than
; built by either adder. The flag sat in the abstraction's gate by adjacency to
; the `if (uf->bvplus_variant)` block underneath it, and the effect was that
; --bb.add-v2=0 abstracted no additions at all -- silently, and often, because
; the fuzz harness draws that flag from its bit-blast group.
;
; The third leg is the other half of the same condition. A wide n-ary addition
; that the abstraction did not decompose is counted as the binary additions the
; decomposition would have made, so that a zero means "no wide addition here"
; rather than "the flag that lowers them was off". That compensating count was
; written in different terms from the gate it compensates for and omitted
; --bv-term-abstraction-plus, so turning that off alone produced exactly the
; unreadable number it exists to prevent: one candidate rather than three.
;
; RUN: %solver --incremental=off -t --bv-term-abstraction=1 --bv-term-abstraction-plus=1 --bv-term-abstraction-compare=0 %s 2>&1 | %OutputCheck --check-prefix=DEFAULT %s
; RUN: %solver --incremental=off -t --bv-term-abstraction=1 --bv-term-abstraction-plus=1 --bv-term-abstraction-compare=0 --bb.add-v2 0 %s 2>&1 | %OutputCheck --check-prefix=ADDV1 %s
; RUN: %solver --incremental=off -t --bv-term-abstraction=1 --bv-term-abstraction-compare=0 --bv-term-abstraction-plus 0 %s 2>&1 | %OutputCheck --check-prefix=NOPLUS %s
;
; DEFAULT: plus=2->2
; ADDV1: plus=2->2
; NOPLUS: plus=3->0
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(declare-fun c () (_ BitVec 64))
(assert (bvult (bvadd a b c) (_ bv100 64)))
(assert (bvugt (bvadd a b) (_ bv5 64)))
(assert (distinct a c))
(check-sat)
(exit)
