
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun v0 () (_ BitVec 1))

(assert (= (concat (_ bv0 1) v0) (_ bv2 2)))




(check-sat)
(exit)


;1126:(EQ 
;  24:0b01010
; 1124:(BVCONCAT 
;    114:0b000
;    1108:array_a2_1))
