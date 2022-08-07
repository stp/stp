; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
(set-info :source | fuzzsmt 0.3 |)
(set-logic  QF_ABV)
(set-info :status sat)
(declare-fun v5572 () (_ BitVec 8))
(declare-fun v5573 () (_ BitVec 8))


(declare-fun v5574 () (_ BitVec 2))
(declare-fun a5575 () (Array (_ BitVec 8) (_ BitVec 8)))

(assert(= v5572 (select (store a5575 v5572 (select a5575 v5572)) v5573)))

; CHECK-NEXT: ^sat
(check-sat)
