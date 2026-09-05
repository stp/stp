; RUN: %solver %s | %OutputCheck %s
;
; A constant's source sort is part of its identity, so the float constant
; 1.0 and the plain bit-vector constant #x3f800000 are distinct interned
; nodes holding identical bits. Any rule that concludes "different cell"
; from "different constant node" -- read-over-write's skip, the array
; transformer's index congruence, the refinement loop's index equalities --
; reads the wrong cell here.
;
; The two directions get a (check-sat) each, so whichever one a broken rule
; reverses shows up as a sat answer rather than being absorbed by the other.
;
; The bit-vector variable pins the same bit pattern into the problem as a
; plain constant as well, so both flavours are live in one manager.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun b () (_ BitVec 32))

(assert (= b #x3f800000))

; Distinct float constants really are distinct cells: 1.0 holds #x01 and
; 2.0 holds #x02, so the read at 1.0 must see #x01. Failing to skip the
; 2.0 write would make this sat.
(push 1)
(assert (= (select (store (store a ((_ to_fp 8 24) #x3f800000) #x01)
                          ((_ to_fp 8 24) #x40000000) #x02)
                   ((_ to_fp 8 24) #x3f800000))
           #x02))
; CHECK: ^unsat$
(check-sat)
(pop 1)

; Equal float constants are the same cell: both writes address 1.0, #x01
; first and #x02 over it, so the read must see #x02. Skipping the second
; write on node identity would answer sat.
(push 1)
(assert (= (select (store (store a ((_ to_fp 8 24) #x3f800000) #x01)
                          ((_ to_fp 8 24) #x3f800000) #x02)
                   ((_ to_fp 8 24) #x3f800000))
           #x01))
; CHECK-NEXT: ^unsat$
(check-sat)
(pop 1)
