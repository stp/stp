; RUN: %solver %s | %OutputCheck %s
;
; A read over a store chain on an array of floats must derive the element
; format through the WRITE node. Regression test: deriveFPFormat had no
; WRITE case, and the unconstrained-variable pass dropped the format from
; its fresh stand-ins, so this well-formed input died with a blank fatal
; error. (The same-index variant is rescued by read-over-write
; simplification and never showed the bug.)
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(assert (fp.isNaN (select (store a i x) j)))
; CHECK: ^sat
(check-sat)
