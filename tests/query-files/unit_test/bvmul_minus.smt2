(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))




; This is always true. 
(assert 
	 (not (= 
		(bvneg (bvmul (bvneg x) (bvneg y) ))
		(bvneg (bvmul  y x ))
		
	))
)


(check-sat)
(exit)

