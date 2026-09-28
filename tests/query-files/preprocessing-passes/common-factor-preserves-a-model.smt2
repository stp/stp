; Taking a factor out of the products of a sum is an identity: multiplication
; distributes over addition modulo 2^w, so neither the value the sum takes nor
; the assignments that give it that value change. Run with -d, so the model is
; rebuilt and checked against the query as written -- an extraction that
; dropped the wrong operand would produce one that does not satisfy it.
; RUN: %solver -s -d --flattening=1 --common-factor=1 %s 2>&1 | %OutputCheck %s
; CHECK: Multiplications saved:[1-9][0-9]*
; CHECK: ^sat$
;
; RUN: %solver -d --common-factor=0 %s | %OutputCheck --check-prefix=OFF %s
; OFF: ^sat$
(set-logic QF_BV)
(declare-fun z () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
(assert (= (bvadd (bvmul z a b) (bvmul z c d)) (_ bv1 8)))
(assert (bvugt z (_ bv1 8)))
(assert (bvugt a (_ bv1 8)))
(assert (distinct a b c d))
(check-sat)
(exit)
