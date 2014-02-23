
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () Bool )
(declare-fun v1 () Bool )
(declare-fun v2 () Bool )

; This should be simplifed to v_0 <=> -v_1 before bitblasing.
(assert (= (xor (not v0) (and  v2 (not v1))) true))

(check-sat)
(exit)


