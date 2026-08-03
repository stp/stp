; RUN: %solver -d --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The counterexample check decides each array equality from the cells
; the model published, and over a float element sort "same cell" is not
; "same bits": SMT-LIB's = on floats is identity of values, and NaN is
; one value with many packings.
;
; This query forces the case. Dividing zero by zero gives a NaN whose
; payload is whatever the lowering produces, the write chain puts it
; into a2 at #b001, and the equality with a2's own base is solved by
; rewriting -- so the model carries that NaN in one operand's cell and
; whatever the base holds in the other's, and the two are equal only
; because both are NaN. Comparing the bits reports the model wrong.
;
; Verified by mutation: making the value comparison bit-exact turns
; this into "an array equality's lowering is true in the model, but the
; model gives the two operands the user equated different contents".
(set-logic QF_ABVFP)
(declare-fun a0 () (Array (_ BitVec 3) (_ FloatingPoint 8 24)))
(declare-fun a1 () (Array (_ BitVec 3) (_ FloatingPoint 8 24)))
(declare-fun z () (_ FloatingPoint 8 24))
(assert (= z ((_ to_fp 8 24) #x00000000)))
(assert (= (select a0 #b001) (fp.div RNE z z)))
(assert (= a0 (store a0 #b001 (fp.div RNE z z))))
(assert (= a1 a0))
(check-sat)
