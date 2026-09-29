; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=off %s | %OutputCheck %s
; The hidden FP addition must be lowered after x's defining binding is
; available. Every untouched cell contains exactly 2.5 + 1.25 = 3.75.
(set-option :produce-models true)
(set-logic QF_ABVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun a () (Array (_ BitVec 8) (_ FloatingPoint 8 24)))
(assert (= a ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24)))
             (fp.add RNE x ((_ to_fp 8 24) #x3fa00000)))))
(assert (= x ((_ to_fp 8 24) #x40200000)))
; CHECK: ^sat$
(check-sat)
; CHECK: #x40700000
(get-value ((fp.to_ieee_bv (select a #x02))))
(push 1)
(assert (not (fp.eq (select a #x02) ((_ to_fp 8 24) #x40700000))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
; CHECK: #x40700000
(get-value ((fp.to_ieee_bv (select a #x02))))
