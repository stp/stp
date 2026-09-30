; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=off %s | %OutputCheck %s
; Array-equality aliases must keep their defining equations until lowering,
; rather than move the unsupported condition into the hidden default.
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (= x y))
(assert (= y (= a b)))
(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8)))
               (ite x #x01 #x02))))
; CHECK: ^sat$
(check-sat)
(push 1)
(assert (= b ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x01)))
(assert (not x))
; CHECK: ^sat$
(check-sat)
; CHECK: #x02
(get-value ((select a #x00)))
(assert (= (select a #x00) #x01))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
