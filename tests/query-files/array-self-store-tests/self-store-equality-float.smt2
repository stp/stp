; RUN: %solver -d %s | %OutputCheck %s
;
; A float-element table entry: the folded read equality is the float =,
; and the model check covers the reconstruction.
;
; CHECK: ^sat
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 8) (_ FloatingPoint 8 24)))
(declare-fun j () (_ BitVec 8))
(assert (= a (store a #x07 ((_ to_fp 8 24) #x3f800000))))
(assert (fp.gt (select a j) ((_ to_fp 8 24) #x3f000000)))
(check-sat)
(exit)
