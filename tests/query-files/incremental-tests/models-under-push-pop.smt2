; Models from the incremental driver: values pinned at pushed levels are
; reported, and a model after the pop no longer honours the popped pin.
; RUN: %solver --incremental --check-sanity %s | %OutputCheck %s
; (--incremental keeps this a DRIVER test: the default pure-BV policy
; leaves this two-check session on the batch path.)
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= x #x42))
(push 1)
(assert (= y #x07))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: \|x\| +#x42
; CHECK: \|y\| +#x07
(get-value (x y))
(pop 1)
(push 1)
(assert (= y #x09))
; CHECK: ^sat
(check-sat)
; CHECK: \|x\| +#x42
; CHECK: \|y\| +#x09
(get-value (x y))
(pop 1)
; after the pop the model is stale, per SMT-LIB
; CHECK: ^unsupported
(get-value (y))
(exit)
