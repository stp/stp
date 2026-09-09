; Two applications the query equates are one application everywhere else:
; the later goes to the earlier, so a term built on either is one term.
;
; A verification query computes the same quantity through two accessors,
; asserts that they agree, and takes the difference of a product of a
; quotient of each. With each side its own application that difference is
; two abstracted 256-bit products of two abstracted quotients, which the
; abstraction refines round after round without ever pinning the free
; dividend; with one application it is a term less itself, and the query
; folds to false before anything is abstracted.
;
; RUN: %solver -s -t --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK: UF: pre-lowering substituted 1 symbol\(s\) and 1 application\(s\)
; CHECK: Abstraction coverage \(candidates -> abstracted\): eq=0->0 compare=0->0 ite=0->0 plus=0->0 mult=0->0 divmod=0->0
; CHECK: ^unsat$
;
; The pass switched off, the two stay apart and each side is its own
; product of its own quotient: four abstracted operations where the merged
; query has none. The solve is not waited for -- with the sides apart it is
; a hard SAT problem over the exact 256-bit encodings, which is the point.
; RUN: %solver -s -t --uninterpreted-functions --incremental=off --uf-propagate-equalities=0 --exit-after-CNF %s 2>&1 | %OutputCheck --check-prefix=APART %s
; APART-NOT: pre-lowering substituted
; APART: Abstraction coverage \(candidates -> abstracted\): eq=2->0 compare=0->0 ite=0->0 plus=0->0 mult=2->2 divmod=2->2
;
; EXPECT: unsat, then no answer (exit after CNF)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 256)) (_ BitVec 256))
(declare-fun g ((_ BitVec 256)) (_ BitVec 256))
(declare-const x (_ BitVec 256))
(declare-const a (_ BitVec 256))
(declare-const b (_ BitVec 256))
(declare-const d (_ BitVec 256))
(assert (= (f x) (g x)))
(assert (= a (bvmul (_ bv10000000000 256) (bvudiv (f x) (_ bv10000000000 256)))))
(assert (= b (bvmul (_ bv10000000000 256) (bvudiv (g x) (_ bv10000000000 256)))))
(assert (= d (bvsub a b)))
(assert (not (= d (_ bv0 256))))
(check-sat)
