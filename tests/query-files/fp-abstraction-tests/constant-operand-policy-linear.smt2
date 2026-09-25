; RUN: %solver --fp-abstraction=true -s %s 2>&1 | %OutputCheck --check-prefix=AUTO %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-constant-operands=on -s %s 2>&1 | %OutputCheck --check-prefix=ADMITTED %s
;
; The same shape as a flux-balance row: every product is one coefficient
; times one variable, standing alone -- nothing this configuration would
; abstract has two operands the blast does not know, and no record's operand
; is another record's result. The automatic policy reads that off the query
; and leaves the products to their exact circuits, which are pruned
; shift-and-adds the solver propagates through, so nothing is abstracted at
; all; asking for them explicitly makes two records of them. Satisfiable
; either way: 3x < 2y has solutions with both in (1, 4).
;
; AUTO: nothing abstracted here computes with two unknowns
; AUTO-NOT: FpAbstraction: 1 abstracted
; AUTO-NOT: FpAbstraction: 2 abstracted
; AUTO: ^sat$
; ADMITTED: FpAbstraction: 2 abstracted
; ADMITTED: ^sat$
(set-logic QF_FP)
(declare-const x Float32)
(declare-const y Float32)
(define-fun one () Float32 (fp #b0 #b01111111 #b00000000000000000000000))
(define-fun two () Float32 (fp #b0 #b10000000 #b00000000000000000000000))
(define-fun three () Float32 (fp #b0 #b10000000 #b10000000000000000000000))
(define-fun four () Float32 (fp #b0 #b10000001 #b00000000000000000000000))
(assert (fp.lt one x))
(assert (fp.lt x four))
(assert (fp.lt one y))
(assert (fp.lt y four))
(assert (fp.lt (fp.mul RNE three x) (fp.mul RNE two y)))
(check-sat)
