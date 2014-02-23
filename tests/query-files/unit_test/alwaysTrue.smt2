
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (= (or c b) b) )
(assert (ite (= (or c b) b) c b ))

(exit)