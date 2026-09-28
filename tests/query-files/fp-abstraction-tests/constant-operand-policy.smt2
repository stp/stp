; RUN: %solver --fp-abstraction=true -s %s 2>&1 | %OutputCheck --check-prefix=AUTO %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-constant-operands=off -s %s 2>&1 | %OutputCheck --check-prefix=DECLINED %s
;
; Two binary32 products: one by a constant, one of two symbols. The second
; is an operation of two operands the blast does not know, so the automatic
; policy takes this for a query that computes with its unknowns rather than
; scaling them by coefficients, and abstracts both. A chain -- a record
; whose operand is another record's result, as in a polynomial evaluated by
; repeated multiplication -- reads the same way, whatever its coefficients
; (restart-without-progress.smt2 is one). Declined, the one by a constant is lowered exactly: a
; shift-and-add network the blast prunes to the constant's set bits and the
; solver propagates through, which is the faster encoding on linear
; arithmetic over coefficients. The report counts the declined ones. Either
; way the query is satisfiable: 3x < xy holds for y above 3.
;
; AUTO-NOT: left exact
; AUTO: FpAbstraction: 2 abstracted
; AUTO: ^sat$
; DECLINED: FpAbstraction: 1 operation\(s\) with a constant operand left exact
; DECLINED: FpAbstraction: 1 abstracted
; DECLINED: ^sat$
(set-logic QF_FP)
(declare-const x Float32)
(declare-const y Float32)
(define-fun one () Float32 (fp #b0 #b01111111 #b00000000000000000000000))
(define-fun three () Float32 (fp #b0 #b10000000 #b10000000000000000000000))
(define-fun four () Float32 (fp #b0 #b10000001 #b00000000000000000000000))
(assert (fp.lt one x))
(assert (fp.lt x four))
(assert (fp.lt one y))
(assert (fp.lt y four))
(assert (fp.lt (fp.mul RNE three x) (fp.mul RNE x y)))
(check-sat)
