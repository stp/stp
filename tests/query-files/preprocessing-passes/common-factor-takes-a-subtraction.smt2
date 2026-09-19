; A subtraction of products reaches the pass as a sum with one addend
; negated, because the factory spells (p - q) as (p + -q) and keeps the
; negation above the product. Since -(x*b) is x*(-b), the negated product
; joins the extraction and the two spellings below have to agree.
; RUN: %solver --flattening=1 --common-factor=1 %s | %OutputCheck %s
; CHECK: ^unsat$
;
; RUN: %solver --common-factor=0 %s | %OutputCheck --check-prefix=OFF %s
; OFF: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (= (bvsub (bvmul x a) (bvmul x b)) (_ bv7 8)))
(assert (= (bvmul x (bvsub a b)) (_ bv9 8)))
(check-sat)
(exit)
