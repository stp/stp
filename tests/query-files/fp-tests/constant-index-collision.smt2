; RUN: %solver %s | %OutputCheck %s
;
; A constant's source sort is part of its identity, so the float constant
; 1.0 and the plain bit-vector constant #x3f800000 are distinct interned
; nodes holding identical bits. Any rule that concludes "different cell"
; from "different constant node" -- read-over-write's skip, the array
; transformer's index congruence, the refinement loop's index equalities --
; reads the wrong cell here.
;
; The array is indexed by floats, so both writes address the same cell: 1.0
; written first, then 2.0 over it. The read must see 2.0, and the assertion
; that it is 1.0 must therefore be unsat. Skipping the second write on node
; identity would answer sat.
;
; The bit-vector variable pins the same bit pattern into the problem as a
; plain constant as well, so both flavours are live in one manager.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun b () (_ BitVec 32))

(assert (= b #x3f800000))
(assert (= (select (store (store a ((_ to_fp 8 24) #x3f800000) #x01)
                          ((_ to_fp 8 24) #x40000000) #x02)
                   ((_ to_fp 8 24) #x3f800000))
           #x02))
(assert (= (select (store (store a ((_ to_fp 8 24) #x3f800000) #x01)
                          ((_ to_fp 8 24) #x3f800000) #x02)
                   ((_ to_fp 8 24) #x3f800000))
           #x01))
; CHECK: ^unsat$
(check-sat)
