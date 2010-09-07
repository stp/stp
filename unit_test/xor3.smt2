
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () Bool )
(declare-fun v1 () Bool )
(declare-fun v2 () Bool )

; Checks that =, that is IFF, will be mixed in with xor.
(assert (xor (not (xor v0 v1))  (= v2 v1)))

(check-sat)
(exit)


