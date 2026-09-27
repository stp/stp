; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: element sort
; A default of the wrong sort is refused.
(set-logic QF_ABV)
(assert (= (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b1) #x02) #x00))
(check-sat)
