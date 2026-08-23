; The exact encoding an abstraction escalates to, installed by the other
; lowering.
;
; When the refinement gives up on a BVMULT it stops enumerating operand pairs
; and encodes the operation, by blasting it into a throwaway AIG, mapping that
; to CNF with the same ABC pass a plain solve uses, and splicing the result
; onto the SAT variables the abstraction has been talking about. The splice
; renumbers every variable of the derived CNF, and where those variables come
; from is exactly what differs between the two parties that mint abstraction
; records: the batch pipeline's whole-formula ToSATAIG, and the persistent,
; per-conjunct encoder the incremental driver uses.
;
; So the batch route being right says nothing about this one. The refiner
; works from the records plus one map from node to SAT variables, and that map
; is built differently here -- addAbstractionOperand harvesting operands and
; records from one blaster, dropped together on a rebuild -- so a splice that
; read the map's entries in the wrong order, or that reached a variable the
; incremental encoder had not registered, would show up here and nowhere else.
;
; Three checks over one stack, two of which escalate, with a push and a pop
; between them so the abstraction is refined, discarded and refined again
; across the same solver. The first product is a factorisation the search has
; to work through; the second is not a square modulo 2^64, so it comes back
; unsat; the third has neither and is satisfied by the bounds alone.
;
; -d re-derives each answer under the published model, so a leg that reported
; sat on a model the raw stack rejects fails here rather than being believed.
;
; RUN: %solver --incremental=on -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=on -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: BV abstraction: encoding BVMULT exactly after [0-9]+ blocking lemmas
; ABSTRACTED: ^sat$
; ABSTRACTED: BV abstraction: encoding BVMULT exactly after [0-9]+ blocking lemmas
; ABSTRACTED: ^unsat$
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
; PLAIN: ^unsat$
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(assert (bvugt a #x0000000000000001))
(assert (bvugt b #x0000000000000001))
(push 1)
(assert (= (bvmul a b) #x7ffffffc80000005))
(check-sat)
(pop 1)
(push 1)
(assert (= (bvmul a b) #x000000000000fff0))
(assert (= a b))
(check-sat)
(pop 1)
(check-sat)
(exit)
