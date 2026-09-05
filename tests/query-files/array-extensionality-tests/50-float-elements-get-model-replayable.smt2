; RUN: %solver -d --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK: define-fun \|a\| \(\) \(Array \(_ BitVec 1\) \(_ FloatingPoint 8 24\)\).*as const \(Array \(_ BitVec 1\) \(_ FloatingPoint 8 24\)\).*\(fp #b[01] #b11111111
; get-model prints a float-element array at its true element sort with
; (fp ...) literals for its cells -- never as a bitvector array -- so
; the define-fun replays against the original declarations.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 1) (_ FloatingPoint 8 24)))
(assert (fp.isNaN (select a #b0)))
(assert (fp.eq (select a #b1) (_ +zero 8 24)))
(check-sat)
(get-model)
