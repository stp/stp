; RUN: not %solver --array-equality %s 2>&1 | %OutputCheck %s
; CHECK: constant-array defaults cannot contain UF applications, Real terms or array-equality conditions
; Real terms are unsupported inside a hidden default, including a Real
; comparison guarding an ITE with otherwise supported bit-vector values.
(set-logic ALL)
(declare-fun x () Real)
(assert (= (select ((as const (Array (_ BitVec 8) (_ BitVec 8)))
                   (ite (< x 0) #x01 #x02))
                  #x00)
           #x01))
(check-sat)
