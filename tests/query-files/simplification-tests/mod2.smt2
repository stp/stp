; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun x () (_ BitVec 15))
(declare-fun y () (_ BitVec 15))

; This should be simplified down.
;2758:(BVEXTRACT 
;   2598:(BVMOD 
;    188:(BVCONCAT 
;      78:0b00000000000000
;      34:(ITE 
;        28:(BVSGT 
;          26:(BVSX 
;            12:v25374
;            24:0x0000000E)
;          16:v25376)
;        30:0b1
;        32:0b0))
;    2594:0b011000111111101)
;  198:0x0000000C
;  200:0x00000005)



; This is always true. 
(assert 
	(=  (concat (_ bv0 5) ((_ extract 9 0) x))
		(bvurem (concat (_ bv0 5) ((_ extract 9 0) x)) (_ bv12000 15) ) 
	)
)

; This is always true. 
(assert 
	(=  (_ bv0 15) 
		(bvudiv (concat (_ bv0 5) ((_ extract 9 0) y)) (_ bv12000 15) ) 
	)
)



; So unconstrained variables don't eliminate immediately.
(assert (not (= x y)))



; CHECK-NEXT: ^sat
(check-sat)
(exit)

