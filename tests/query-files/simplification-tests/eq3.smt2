; RUN: %solver %s | %OutputCheck %s

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)

(declare-fun v0 () (_ BitVec 20))
(declare-fun v1 () (_ BitVec 20))
(declare-fun v2 () (_ BitVec 20))


(assert (and 
			 (= (bvneg v0) (bvudiv v1 v2))
			 (= (bvadd v0 (bvudiv v1 v2)) (bvadd v1 v2) )
	    )
)


(declare-fun v01 () (_ BitVec 20))
(declare-fun v11 () (_ BitVec 20))
(declare-fun v21 () (_ BitVec 20))


(assert (and 
			 (= (bvnot v01) (bvudiv v11 v21))
			 (= (bvadd v01 (bvudiv v11 v21)) (bvadd v11 v21) )
	    )
)


(declare-fun v02 () (_ BitVec 20))
(declare-fun v12 () (_ BitVec 20))
(declare-fun v22 () (_ BitVec 20))


(assert (and 
			 (= v02 (bvnot  v12))
			 (= v02 (bvnot  v22))
	    )
)


(declare-fun v03 () (_ BitVec 20))
(declare-fun v13 () (_ BitVec 20))
(declare-fun v23 () (_ BitVec 20))


(assert (and 
			 (= v03 (bvneg  v13))
			 (= v03 (bvneg  v23))
	    )
)


; CHECK-NEXT: ^sat
(check-sat)
(exit)

