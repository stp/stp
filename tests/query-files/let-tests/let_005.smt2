; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status sat)

(declare-fun y () (_ BitVec 5))


; y must <> 6 in a satisfying solution.
(assert 
	(not
		(=
			(let 
				(
					(x (_ bv13 5) )
					(y (_ bv6 5) )
				)
				x
			)	
			(let 
				((x (_ bv7 5) ) )
				(bvadd x y)
			)	
		)
	)
)

; CHECK-NEXT: ^sat
(check-sat)