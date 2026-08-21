; A transitivity conflict has to be explained by the chain that caused it.
;
; --bv-eq-abstraction replaces an equality by a free Boolean, and the
; congruence phase of refinement refutes a candidate model that asserts a
; chain of equalities connecting the two sides of a disequality it also
; asserts. It hands the solver (~e1 | ... | ~ek | d), which is a theorem only
; if e1..ek really are a chain between d's two sides. They were read off the
; union-find, which links class representatives by rank and so records the
; merge of a=b then b=c as a single link out of c labelled b=c -- the path
; from c to the root never mentions a=b. The clause emitted for a!=c was then
; (~(b=c) | a=c): an implication equality does not license, and one that
; eliminates every model where b=c and a differs from both.
;
; RoundingMode reaches it immediately. The sort has five values in a five-bit
; carrier, so every symbol of it carries a validity constraint that is a
; disjunction of equalities against the mode constants, and a candidate model
; routinely asserts several of those at once through the one symbol. Three
; pairwise distinct modes exist -- RTZ, RNE, RNA will do -- so this is
; satisfiable, and STP answered unsat.
;
; The width floor is why the default configuration never showed it: the
; carrier is five bits wide and the floor is sixty-four, so the abstraction
; never reaches a rounding mode unless the floor is lowered.
;
; RUN: %solver --bv-eq-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --bv-eq-abstraction=1 --bv-abstraction-width=1 --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_FP)
(declare-const x0 RoundingMode)
(declare-const x1 RoundingMode)
(assert (distinct RTZ x1 x0))
(check-sat)
(exit)
