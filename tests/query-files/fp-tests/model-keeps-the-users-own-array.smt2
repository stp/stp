; RUN: %solver %s | %OutputCheck %s
;
; The companion to unspecified-array-absent-from-model.smt2: hiding the
; introduced array must not hide the input's own. Both are arrays, both reach
; the printer as READ entries, and only the introduced one is registered --
; so filtering on "is an array read" rather than on "is introduced" would
; pass that test and break this one.
; CHECK: ^sat
; CHECK-L: (define-fun |a| (_ BitVec 4) (_ BitVec 8) #x3 #x2A)
; CHECK-NOT-L: @fp_unspecified
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const x (_ FloatingPoint 8 24))
(assert (= (select a #x3) #x2a))
(assert (= ((_ fp.to_ubv 8) RNE x) #x07))
(check-sat)
(get-model)
