; Refinement profiling separates the initial SAT call from theory-driven
; re-solves. The inconsistent aliased reads deterministically require one
; congruence refinement round with the default backend.
; RUN: %solver --incremental --incremental-profile %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(assert (= (select a i) #x01))
(push 1)
(assert (= (select a j) #x02))
(assert (= i j))
; CHECK: Incremental profile: check=1.*prepare-us=[0-9]+ encode-us=[0-9]+ read-seed-us=[0-9]+ registry-us=[0-9]+.*initial-sat-us=[0-9]+ refinement-sat-us=[0-9]+
; CHECK: Incremental profile cbp/backend: check=1.*driver-clauses=[1-9][0-9]* refinement-clauses=[1-9][0-9]* retained-clauses=[1-9][0-9]* live-clauses=[1-9][0-9]* exact-live-clauses=[1-9][0-9]* peak-live-clauses=[1-9][0-9]* sat-calls=2 refinement-sat-calls=1 refinement-rounds=1
; CHECK: Incremental profile total: checks=1.*driver-clauses=[1-9][0-9]* refinement-clauses=[1-9][0-9]* retained-clauses=[1-9][0-9]* live-clauses=[1-9][0-9]* peak-live-clauses=[1-9][0-9]* sat-calls=2 refinement-sat-calls=1 refinement-rounds=1
; CHECK: ^unsat
(check-sat)
(exit)
