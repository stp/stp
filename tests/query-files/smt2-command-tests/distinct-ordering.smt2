; A distinct whose operands are variables occurring nowhere else is ordered.
;
; Every permutation of such operands maps the formula to itself, so requiring
; them to increase discards n!-1 copies of each answer and keeps one. What is
; left is n-1 comparisons in place of n(n-1)/2 disequalities, and, more to the
; point, an ordering the bit-blaster is told rather than made to find: three
; hundred unconstrained 32-bit variables under one distinct are decided in
; 0.2 seconds rather than 172 (RelWithDebInfo, CaDiCaL).
;
; The four blocks are the guard's decision, not four shapes of the same case.
; Only the first is symmetric. In the second, b is compared outside the
; distinct, so the operands are no longer interchangeable and imposing
; a < b < c would contradict b < a -- reporting unsat where the answer is sat.
; In the third the distinct is negated, where the chain is the weaker claim,
; so a model of the rewritten formula need not be a model of the input; the
; rewrite declines rather than publish a model it cannot stand behind. That
; block is pinned by the absence of the stats line alone: negated or not, the
; answer is sat either way.
;
; The fourth block is the model. Four two-bit variables have exactly one
; increasing assignment, so the chain names it outright, which is both what
; makes the values worth checking -- they are a model of the unrewritten
; distinct, all four differing -- and a reminder that the shape of a published
; model is now canonical where it used to be any of the 24 permutations.
;
; RUN: %solver -s --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK: Ordered 1 symmetric distinct group\(s\)
; CHECK: ^sat
; CHECK: SYMMETRIC-DONE
; CHECK-NOT: Ordered
; CHECK: ^sat
; CHECK: LEAKED-DONE
; CHECK-NOT: Ordered
; CHECK: ^sat
; CHECK: NEGATED-DONE
; CHECK: Ordered 1 symmetric distinct group\(s\)
; CHECK: ^sat
; CHECK: \|a\| +#b00
; CHECK: \|b\| +#b01
; CHECK: \|c\| +#b10
; CHECK: \|d\| +#b11
;
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(declare-const keep (_ BitVec 8))
(assert (distinct a b c))
(assert (bvult keep #x10))
(check-sat)
(echo "SYMMETRIC-DONE")
(reset)
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (distinct a b c))
(assert (bvult b a))
(check-sat)
(echo "LEAKED-DONE")
(reset)
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (not (distinct a b c)))
(check-sat)
(echo "NEGATED-DONE")
(reset)
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-const c (_ BitVec 2))
(declare-const d (_ BitVec 2))
(assert (distinct a b c d))
(check-sat)
(get-value (a b c d))
