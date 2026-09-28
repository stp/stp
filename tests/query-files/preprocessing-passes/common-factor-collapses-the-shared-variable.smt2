; The reported shape: every product of the sum multiplies by the same
; variable, and no two of them share anything else. With the variable
; factored out it occurs once, which is what lets the rest of the pipeline
; see it is unconstrained; before the extraction the sum is four
; three-operand products and reaches the SAT solver as written.
; RUN: %solver -s -d --flattening=1 --common-factor=1 %s 2>&1 | %OutputCheck %s
; CHECK: Multiplications saved:[1-9][0-9]*
; CHECK: ^sat$
;
; RUN: %solver -d --common-factor=0 %s | %OutputCheck --check-prefix=OFF %s
; OFF: ^sat$
(set-logic QF_BV)
(declare-fun z54 () (_ BitVec 5))
(declare-fun c_2 () (_ BitVec 5))
(declare-fun c_3 () (_ BitVec 5))
(declare-fun c_5 () (_ BitVec 5))
(declare-fun c_6 () (_ BitVec 5))
(declare-fun c31 () (_ BitVec 5))
(declare-fun c32 () (_ BitVec 5))
(declare-fun c34 () (_ BitVec 5))
(declare-fun c35 () (_ BitVec 5))
(assert (= (bvadd (bvmul (_ bv31 5) (bvmul c_3 (bvmul c34 z54)))
                  (bvadd (bvmul (_ bv31 5) (bvmul c_2 (bvmul c35 z54)))
                         (bvadd (bvmul (_ bv31 5) (bvmul c31 (bvmul c_6 z54)))
                                (bvmul (_ bv31 5) (bvmul c32 (bvmul c_5 z54))))))
           (_ bv0 5)))
(assert (bvugt z54 (_ bv0 5)))
(assert (distinct c_2 c_3 c_5 c_6))
(check-sat)
(exit)
