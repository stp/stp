(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun x () (_ BitVec 15))
(declare-fun y () (_ BitVec 15))



; This is always true. 
(assert 
	(bvuge
		(_ bv9 15)
		(bvurem (bvand x y) (_ bv10 15))
	)
)

; So unconstrained variables don't eliminate immediately.
(assert (not (= x y)))



(check-sat)
(exit)

