; The solver's own symbols are not entries of the model.
;
; BBfpSignificandProduct mints @fp_significand_<2*sb>_l and _r through the
; factory, as a shape template for the significand multiplier -- symbols rather
; than constants, so that a folding factory cannot collapse the product. Being
; real interned symbols they were in STPMgr::getSymbols(), and they are not in
; the introduced set (their name is their identity, as the partial-FP cells'
; is), so nothing stopped the model publishing them:
;
;   (define-fun |@fp_significand_48_r| () (_ BitVec 48) #x000000000000)
;
; An input cannot declare a name with a reserved '@' prefix, so a symbol that
; carries one is never the query's. The frame lookup the model now goes through
; declines them for free: they were never declared.
; RUN: %solver %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK: define-fun \|[ab]\|
; CHECK-NOT: @fp_significand
; CHECK-NOT: define-fun \|@
(set-option :produce-models true)
(set-option :incremental on)
(set-logic QF_FP)
(declare-fun a () Float32)
(declare-fun b () Float32)
(assert (fp.isNormal (fp.mul RNE a b)))
(check-sat)
(get-model)
(exit)
