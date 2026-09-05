; The schema that says the most, on a query that has to be searched.
;
; An operand whose value is a power of two, or the negation of one, turns the
; whole product into a shift: a = 2^k -> t = b << k and
; a = -2^k -> t = (-b) << k. Where a blocking lemma fixes both operands and
; rules out the one pair, either schema fixes one and leaves the other free,
; so it rules out 2^64 pairs at the default width -- and it is the *whole*
; answer for that operand value, not an approximation of it. The refinement
; therefore always takes one when it applies.
;
; The candidates a solver offers are its own business, so this does not pin
; which round a shift lemma lands on -- nor, since the bounded facts are now
; offered first, that one is reached at all. A backend whose candidates the
; trailing-zero and registry facts refute first settles the query without
; ever holding a power-of-two operand: CaDiCaL reaches the shift here and
; Riss does not, and both are correct refinements.
;
; What is pinned is that a schema is what refined it, and that the search
; still comes back with the model the unabstracted encoding gives. That a
; power-of-two operand IS taken as the shift once the bounded facts are in
; is a property of the chooser rather than of any one search, and
; BVMultSchema_Test.APowerOfTwoOperandIsTakenAsTheShiftOnceTheBoundedFactsAreIn
; checks it exhaustively over every exponent, operand and wrong product,
; without a solver in the way.
;
; -d re-derives the query under the published model, so the sat is a real one
; and not merely a line that was printed.
;
; RUN: %solver --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=SCHEMAS %s
; RUN: %solver --incremental=off -d --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-schemas=0 %s 2>&1 | %OutputCheck --check-prefix=NOSCHEMAS %s
; RUN: %solver --incremental=off -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; SCHEMAS-NOT: Fatal Error
; SCHEMAS-NOT: Assertion
; SCHEMAS: BV abstraction: BVMULT [a-z0-9-]+ lemma over operand [01]
; SCHEMAS: ^sat$
;
; NOSCHEMAS-NOT: Fatal Error
; NOSCHEMAS: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(assert (= (bvmul a b) #x7ffffffc80000005))
(assert (bvugt a #x0000000000000001))
(assert (bvugt b #x0000000000000001))
(check-sat)
