
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () (_ BitVec 20))
(declare-fun v1 () Bool)


(assert (or v1 (= (bvsmod v0 (bvnot v0)) (_ bv23211 20) )))




(check-sat)
(exit)


