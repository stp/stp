; Addition schemas must be stated over the semantic operands. The bit-blaster
; records (bvneg x) as the proxy for x plus an operand-negated flag, so a
; schema emitted directly over that proxy would constrain x + s while the
; abstracted result stands for (-x) + s.
;
; Pin x[1:0] = 01, s[1:0] = 00 and require result[1] = 1. This is satisfiable:
; the low two bits of -x are 11. Some addition fact is violated by whatever
; candidate comes back and the schema then says what the sum is over -x. If
; it were accidentally spliced over raw x instead, it would instead force
; result[1] to zero and turn this satisfiable query unsat -- which is why
; `sat` below is the assertion that catches the bug.
;
; Which fact fires is not pinned. It depends on the candidate, and so on the
; backend: CaDiCaL 3.0.1 violates ADD_ZERO here and 2.1.3 violates the
; overflow fact over the other operand reading. What matters is that a
; schema is what refined it, which is the difference between the two legs
; below.
;
; RUN: %solver --incremental=off --disable-simplifications -s --bv-abstraction-width=1 --bv-term-abstraction=1 --bv-term-abstraction-plus=1 --bv-term-abstraction-schema-groups=add %s 2>&1 | %OutputCheck --check-prefix=SCHEMAS %s
; RUN: %solver --incremental=off --disable-simplifications -s --bv-abstraction-width=1 --bv-term-abstraction=1 --bv-term-abstraction-plus=1 --bv-term-abstraction-schemas=0 --bv-term-abstraction-schema-groups=add %s 2>&1 | %OutputCheck --check-prefix=NOSCHEMAS %s
; RUN: %solver --incremental=off --disable-simplifications %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; SCHEMAS-NOT: Fatal Error
; SCHEMAS-NOT: Assertion
; SCHEMAS: BV abstraction: BVPLUS [a-z0-9-]+ lemma over operand [01]
; SCHEMAS: ^sat$
;
; NOSCHEMAS-NOT: BVPLUS [a-z0-9-]+ lemma
; NOSCHEMAS: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(assert (= ((_ extract 0 0) x) #b1))
(assert (= ((_ extract 1 1) x) #b0))
(assert (= ((_ extract 0 0) s) #b0))
(assert (= ((_ extract 1 1) s) #b0))
(assert (= ((_ extract 1 1) (bvadd (bvneg x) s)) #b1))
(check-sat)
