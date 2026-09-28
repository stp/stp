; The factored spelling and the distributed one are the same value, so they
; cannot be two different constants. The first sum is what the pass rewrites,
; and it rewrites it into the second query's term; if it took the wrong
; operand out the two would no longer have to agree and this would be
; satisfiable.
; RUN: %solver --flattening=1 --common-factor=1 %s | %OutputCheck %s
; CHECK: ^unsat$
;
; RUN: %solver --common-factor=0 %s | %OutputCheck --check-prefix=OFF %s
; OFF: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (= (bvadd (bvmul x a) (bvmul x b)) (_ bv7 8)))
(assert (= (bvmul x (bvadd a b)) (_ bv9 8)))
(check-sat)
(exit)
