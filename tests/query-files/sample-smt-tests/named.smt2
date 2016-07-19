; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat

(set-logic QF_AUFBV )
(declare-fun arr () (Array (_ BitVec 32) (_ BitVec 32) ) )
(push 1)
(assert 
		(!
			(bvslt  
					(! (select  arr (_ bv0 32) ) :named N0) 
					(! (! (bvadd  (_ bv1 32) N0 ) :named B1) :named B2)
			) 
		:named B3
		)
)
(assert
	(! (distinct (! N0 :named B5) B1) :named B4)
)

(assert (= B3 B4))

(check-sat)
(get-value (N0 B1 B2 B3 B4 B5))
(pop 1)
; Have popped away N0, can redefine it now..
(declare-fun N0 () (Array (_ BitVec 32) (_ BitVec 32) ) )
(exit)