(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () (_ BitVec 24))
(declare-fun v1 () (_ BitVec 24))
(declare-fun v2 () (_ BitVec 24))
(declare-fun v3 () (_ BitVec 24))


; The

;  1107176:(EQ 
;    119800:0x00000001
;    1107174:(BVCONCAT 
;      119164:0x00000
;      1107170:(BVCONCAT 
;        1107166:(BVEXTRACT 
;          985666:(BVEXTRACT 
;            985530:unconstrained_36910
;            120104:0x00000007
;            118910:0x00000000)
;          213036:0x00000003
;          118910:0x00000000)
;        985668:(BVEXTRACT 
;          985530:unconstrained_36910
;          119266:0x0000000F
;          120112:0x00000008))))


(assert  
	(=	(_ bv1 24)
		( concat 	
				(_ bv0 12)				
				( concat 	
					((_ extract 3 0) ((_ extract 7 0) v0))
					((_ extract 15 8) v0)
				)
		)
	)
)

(check-sat)
(exit)

