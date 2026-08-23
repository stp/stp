; The schema that says the most, on a query that has to be searched.
;
; An operand whose value is a power of two turns the whole product into a
; shift: a = 2^k -> t = b << k. Where a blocking lemma fixes both operands and
; rules out the one pair, this fixes one and leaves the other free, so it
; rules out 2^64 pairs at the default width -- and it is the *whole* answer
; for that operand value, not an approximation of it. The refinement therefore
; always takes it when it applies.
;
; The candidates a solver offers are its own business, so this does not pin
; which round the shift lemma lands on, only that a factorisation the search
; genuinely works through reaches one and still comes back with the model the
; unabstracted encoding gives. -d re-derives the query under the published
; model, so the sat is a real one and not merely a line that was printed.
;
; RUN: %solver --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=SCHEMAS %s
; RUN: %solver --incremental=off -d --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-schemas=0 %s 2>&1 | %OutputCheck --check-prefix=NOSCHEMAS %s
; RUN: %solver --incremental=off -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; SCHEMAS-NOT: Fatal Error
; SCHEMAS-NOT: Assertion
; SCHEMAS: BV abstraction: BVMULT power-of-two lemma over operand [01]
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
