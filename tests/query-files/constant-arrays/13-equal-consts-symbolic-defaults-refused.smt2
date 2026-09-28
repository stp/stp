; RUN: not %solver --array-equality %s 2>&1 | %OutputCheck %s
; CHECK: must be a value, and this one depends on v
; A constant array's default must be a value, so an equality between two over
; variables is refused rather than read as the equality of the variables.
(set-logic QF_ABV)
(declare-fun v () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (= ((as const (Array (_ BitVec 8) (_ BitVec 8))) v) ((as const (Array (_ BitVec 8) (_ BitVec 8))) w)))
(assert (not (= v w)))
(check-sat)
