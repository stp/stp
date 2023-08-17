; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status unsat)


; Let in the binding part of another let with shadowing.
(assert 
	(not
		(let
			(
				(x (_ bv7 5))
			)
			(let 
				(
					(y 
						(let
							(
								(y (_ bv6 5))
								(x (bvadd x (_ bv10 5)))
							)
							(bvadd y (_ bv1 5))
						)
					)
				)
				(= y x)
			)	
		)
	)
)

; CHECK-NEXT: ^unsat
(check-sat)