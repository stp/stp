; --ackermanize inside the incremental driver: arrays are compiled away
; eagerly -- each new read carries a nested if-then-else over the reads
; already seen, a naturally monotone encoding -- and the per-array read
; lists persist across check-sats, so pair coverage holds session-wide.
; Same rounds and answers as arrays-rounds.smt2, no refinement loop.
; RUN: %solver --incremental --ackermanize -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --ackermanize --check-sanity -s %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(assert (= (select a i) #x01))
(push 1)
(assert (= (select a j) #x02))
(assert (= i j))
; CHECK: ^unsat
(check-sat)
(pop 1)
(push 1)
; the same read returns after the pop: its encoding is reused wholesale
(assert (= (select a j) #x02))
(assert (distinct i j))
; CHECK: Incremental: encoded 1 new conjuncts
; CHECK: ^sat
(check-sat)
(pop 1)
; CHECK: ^sat
(check-sat)
(push 1)
(assert (= (select (store a i #x07) i) #x08))
; CHECK: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert (distinct i j))
(assert (= (select (store a j #x07) i) #x01))
; CHECK: ^sat
(check-sat)
(pop 1)
(assert (= (select a #x30) #x33))
(push 1)
(assert (= i #x30))
; CHECK: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert (= j #x30))
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
