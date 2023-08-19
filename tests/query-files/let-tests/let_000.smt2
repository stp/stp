; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :status sat)

; variables get bound twice
(assert 
	(let 
		((x (_ bv1 6) ) (y (_ bv5 6) ))
		(let 
			((x (_ bv0 6) )  (y x ))
			(not (= x y)) 
		)
	)
)
; CHECK-NEXT: ^sat
(check-sat)