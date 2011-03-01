
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)

; These can be simplified by considering the context
; of the ITES they contain. 

(declare-fun v0 () (_ BitVec 20))
(declare-fun v1 () (_ BitVec 20))
(declare-fun v2 () (_ BitVec 20))

; The first disjunct is unsatisfiable. So it should be removed. Making v0 or v1 unconstrained.

(assert (or 
			 (= (_ bv1 20) (ite (= (_ bv2 20) (bvudiv v0 v1)) (_ bv3 20) (_ bv5 20)  ) )
			 (= (bvadd v0 v1) (_ bv1 20) )
	    )
)


(check-sat)
(exit)

