; RUN: not %solver --array-equality %s 2>&1 | %OutputCheck %s
; CHECK: constant-array defaults cannot contain UF applications, Real terms or array-equality conditions
; UF applications in defaults need preparation before the hidden default is
; visited, so reject this form through the parser's normal error response.
(set-logic QF_AUFBV)
(declare-fun x () (_ BitVec 8))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (= (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) (f x))
                   #x00)
           #x01))
(check-sat)
