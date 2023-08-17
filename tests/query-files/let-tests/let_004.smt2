; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status sat)

(declare-fun x () (_ BitVec 15))

(declare-fun y () (_ BitVec 5))
(declare-fun z () (_ BitVec 15))

; two fresh variables, neither appear in the term.
(assert 
	(let 
		((fresh0 (_ bv0 5) ) (fresh1 (_ bv0 5) ))
		(= y (_ bv0 5)) 
	)
)

; already defined variable that doesn't appear in the term.
(assert 
	(let 
		((x (_ bv0 5) ))
		(= y (_ bv0 5)) 
	)
)

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

; bind inside an operation.
(assert 
	(not
		(=
			(let 
				((x (_ bv6 5) ))
				x
			)	
			(let 
				((x (_ bv7 5) ))
				x
			)	
		)
	)
)

;(declare-fun b () Bool)
;(declare-fun B () Bool)
;( assert b)
;( assert B)


; All combinations with pipes.
(assert 
	(not
		(let ((b false))
			b
		)
	)
)

(assert 
	(not
		(let ((|b| false))
			b
		)
	)
)

(assert 
	(not
		(let ((|b| false))
			|b|
		)
	)
)

(assert 
	(not
		(let ((b false))
			|b|
		)
	)
)

; whitespace is part of the name
(assert 
	(not
		(let ((| b | false))
			| b |
		)
	)
)

; case sensitive, with re-assignment and type change.
(assert 
	(not
		(let ((B (_ bv0 5)))
			(let ((| b| true) (b true) (B false))
				|B|
			)
		)
	)
)

; The empty symbol.
(assert 
	(not
		(let ((|| false))
			||
		)
	)
)

; Should fail because binds "a" twice.
;(assert (not (let ((a false) (a false)) a)))

; CHECK-NEXT: ^sat
(check-sat)