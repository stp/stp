(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun x () (_ BitVec 10))
(declare-fun y () (_ BitVec 10))


; 
(assert 
	 (bvult
		(bvudiv x  y )
		(_ bv1 10)
	)
)

(assert (not (bvult x y)))


(check-sat)
(exit)

