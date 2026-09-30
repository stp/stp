; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=off %s | %OutputCheck %s
; Formal parameters inside a constant-array default must be freshened and
; substituted at each application. Both equalities cannot hold together.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(define-fun all-cells ((x (_ BitVec 8))) Bool
  (= a ((as const (Array (_ BitVec 8) (_ BitVec 8))) x)))
(assert (all-cells #x01))
; CHECK: ^sat$
(check-sat)
(push 1)
(assert (all-cells #x02))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
; The scalar default can itself contain a read over another constant array;
; substitution must follow every hidden default, and retain shared nodes.
(define-fun nested-cells ((x (_ BitVec 8))) Bool
  (= a ((as const (Array (_ BitVec 8) (_ BitVec 8)))
         (select (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) x)
                        #x00 #xff)
                 #x01))))
(assert (nested-cells #x03))
; CHECK: ^unsat$
(check-sat)
