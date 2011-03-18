(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun x () (_ BitVec 10))
(declare-fun y () (_ BitVec 15))
(declare-fun z () (_ BitVec 55))

(assert (not (=  ((_ sign_extend 25) (bvmul ((_ sign_extend 20) x) ((_ sign_extend 15) y)))
		(bvmul ((_ sign_extend 45) x) ((_ sign_extend 40) y) ) )
)
)

(declare-fun a () (_ BitVec 15))
(declare-fun b () (_ BitVec 55))
(assert  (= (_ bv44444444444444444 65) (bvadd ((_ sign_extend 50 ) a ) ((_ sign_extend 10 ) b  ))))


(check-sat)
(exit)

	