; RUN: %solver --aig-rewrite-passes=1 %s | %OutputCheck %s
(set-logic QF_ABV)
(set-info :status unsat)
; Dar_ManRewrite() cleans up dangling nodes on entry but not on exit, so a node
; that Dar_LibBuildBest() built and then lost the last reference to survives the
; pass with no fanout. Aig_ManDupDfs() copies from the CO down, so it drops such
; a node -- and then asserts that it dropped none. This query is a reduction of
; a fuzzer case that leaves exactly one node behind, which aborted an assertions
; build before dag_aware_aig_rewrite() cleaned up between the two calls.
;
; Reduced from fuzzsmt QF_ABV output, so the term is arbitrary; what matters is
; that it survives preprocessing intact enough to reach AIG rewriting.
(declare-fun v () (_ BitVec 13))
(declare-fun v2 () (_ BitVec 15))
(declare-fun v24 () (_ BitVec 16))
(declare-fun a () (Array (_ BitVec 12) (_ BitVec 10)))
(assert (and
  (distinct
    (bvsle v24 (_ bv0 16))
    (= (bvsmulo v2 ((_ sign_extend 12) (bvsmod (_ bv3 3) ((_ sign_extend 2) (ite (distinct v24 (_ bv0 16)) (_ bv1 1) (_ bv0 1))))))
       (or (bvumulo (_ bv0 15) (_ bv0 15))
           (bvsmulo ((_ zero_extend 1) v) ((_ sign_extend 11) (bvneg (bvsmod (_ bv1 3) ((_ sign_extend 2) (ite (distinct v24 (_ bv0 16)) (_ bv1 1) (_ bv0 1)))))))))
    (= (bvsge ((_ sign_extend 12) (bvneg (bvsmod (_ bv1 3) ((_ sign_extend 2) (ite (distinct v24 (_ bv0 16)) (_ bv1 1) (_ bv0 1)))))) v2)
       (or (bvuge (_ bv0 14) ((_ zero_extend 13) (ite (distinct v24 (_ bv0 16)) (_ bv1 1) (_ bv0 1))))
           (bvuge (select a (_ bv1 12)) ((_ zero_extend 7) (bvneg (bvsmod (_ bv1 3) ((_ sign_extend 2) (ite (distinct v24 (_ bv0 16)) (_ bv1 1) (_ bv0 1))))))))))
  (= (bvnego (_ bv0 1))
     (bvsle v2 ((_ sign_extend 14) (ite (distinct v24 (_ bv0 16)) (_ bv1 1) (_ bv0 1))))
     (bvnego (ite (bvsmulo (select a (_ bv1 12)) ((_ sign_extend 7) (bvneg (bvsmod (_ bv1 3) ((_ sign_extend 2) (ite (distinct v24 (_ bv0 16)) (_ bv1 1) (_ bv0 1))))))) (_ bv1 1) (_ bv0 1))))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
