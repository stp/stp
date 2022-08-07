; RUN: %solver --exit-after-CNF %s | %OutputCheck %s

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () (_ BitVec 2))

(assert (bvsgt (_ bv0 2) (bvnot (bvand (_ bv1 2) v0)) ))




; CHECK-NEXT: ^sat
(check-sat)
(exit)

; Something like this..
;1498:(BVSGT 
;  1496:(BVCONCAT 
;    538:0b00000000000000
;    1494:(ITE 
;      1486:(BVGE 
;        1482:(BVSX 
;          1480:array_a7_0
;          62:0x00000008)
;        12:v0)
;      54:0b1
;      56:0b0))
;  286:(BVNEG 
;    284:(BVAND 
;      274:0b000000001001110
;      20:v4)))
