; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: must be a value, and this one depends on z
; A constant array's default must be a value. The engine keeps the default
; beside the array's symbol, where no preprocessing pass sees it: z = #b11 was
; substituted away while the array still named z, and this unsatisfiable
; problem came back sat with z set to #b00.
(set-logic QF_ABV)
(declare-fun z () (_ BitVec 2))
(assert (= ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00)
           (store ((as const (Array (_ BitVec 2) (_ BitVec 2))) z) #b00 #b00)))
(assert (= z #b11))
(check-sat)
