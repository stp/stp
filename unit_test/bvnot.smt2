(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun x () (_ BitVec 6))



; This is always true. 
(assert 
	 (=
		(bvnot x  )
		x
	)
)


(check-sat)
(exit)

