; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status sat)

; Let in the binding part of another let with shadowing.
(assert 
	(let
		(
			(x (_ bv7 5))
		)
		(let
			(
				(x (bvadd x (_ bv10 5)))
			)
			(= (_ bv17 5) x)
		)
	)
)
; CHECK-NEXT: ^sat
(check-sat)