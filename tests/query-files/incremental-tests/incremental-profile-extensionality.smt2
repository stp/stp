; Extensionality emits its refinement lemma directly through SATSolver. The
; solver-wide submission counter must include that work in both the check and
; session totals, while the dedicated field identifies the refinement share.
; The budget is pinned to zero to keep this on the refinement path: the
; query is now affordable enough for the eager arm, which retires the
; records and reports no rounds. The counters below are what refinement
; does, which is what this profiles.
; RUN: %solver --incremental --array-equality --incremental-profile --array-ackermann-budget=0 %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(push 1)
(assert (= a b))
(assert (= (select a #x1) #x11))
(assert (= (select b #x1) #x22))
; CHECK: Incremental profile cbp/backend: check=1.*driver-clauses=323 refinement-clauses=35 retained-clauses=323 live-clauses=323 exact-live-clauses=323 peak-live-clauses=323.*refinement-rounds=1 ext-preprocesses=1.*extensionality=1
; CHECK: Incremental profile total: checks=1.*driver-clauses=323 refinement-clauses=35 retained-clauses=323 live-clauses=323 peak-live-clauses=323.*refinement-rounds=1 ext-preprocesses=1
; CHECK: ^unsat
(check-sat)
(pop 1)
; CHECK: Incremental profile cbp/backend: check=2.*driver-clauses=0 refinement-clauses=0 retained-clauses=323 live-clauses=0 exact-live-clauses=0 peak-live-clauses=323.*refinement-rounds=0 ext-preprocesses=0.*extensionality=0
; CHECK: Incremental profile total: checks=2.*driver-clauses=323 refinement-clauses=35 retained-clauses=323 live-clauses=0 peak-live-clauses=323.*refinement-rounds=1 ext-preprocesses=1
; CHECK: ^sat
(check-sat)
(exit)
