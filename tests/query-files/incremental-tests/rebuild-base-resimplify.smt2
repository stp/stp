; The rebuild boundary runs a GLOBAL simplification pass over the base
; conjunction -- the whole-formula constant propagation and
; unconstrained-variable elimination the driver forgoes per query --
; because everything re-encodes from scratch there anyway and the base
; never retracts. Pins:
;
; 1. The relief-valve rebuild reports the pass and the base collapses.
; 2. A base variable it eliminated answers get-value by replaying its
;    definition -- even though the variable's pre-rebuild bits are still
;    in the bit-blast memo, they are no longer encoded, and trusting
;    them would answer a default.
; 3. Later content mentioning an eliminated variable gets its constraint
;    restored: an implied equation returns as itself (the contradiction
;    is seen), while a variable the unconstrained pass dropped gets its
;    ORIGINAL conjunct back, not the witness value the model replay
;    uses -- new content may pick any value the original allows.
; RUN: %solver -s --incremental --incremental-reencode-limit 1 --check-sanity %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --incremental-auto-engage-at 1 --incremental-reencode-limit 1 --check-sanity %s 2>&1 | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b1 () (_ BitVec 8))
(declare-fun b2 () (_ BitVec 8))
(declare-fun c2 () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun y1 () (_ BitVec 8))
(declare-fun y2 () (_ BitVec 8))
(declare-fun y3 () (_ BitVec 8))
(declare-fun y4 () (_ BitVec 8))
(declare-fun y5 () (_ BitVec 8))
(declare-fun y6 () (_ BitVec 8))
; a definitional chain the rebuild pass collapses; a is pinned to zero
; so the replayed values are deterministic. c2 is dropped as
; unconstrained under a bound that allows two values.
(assert (= b1 (bvadd a #x01)))
(assert (= b2 (bvadd b1 #x01)))
(assert (bvult a #x01))
(assert (bvult c2 #x02))
; heavy throwaway rounds accumulate dead clause mass -- each a distinct
; multiplier circuit -- until the valve's mass ratio trips
(push 1)
(assert (bvugt (bvmul y1 y1) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y2 y2) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y3 y3) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y4 y4) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y5 y5) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y6 y6) #x03))
; five dead rounds exceed four times the peak working set: the valve
; fires at this solve and the rebuild runs the global base pass
; CHECK: base re-simplified at rebuild
; CHECK: ^sat
(check-sat)
(pop 1)
; a fresh base conjunct invalidates the verdict cache so the next check
; really solves against the rebuilt encoding
(assert (bvule y #xff))
; CHECK: ^sat
(check-sat)
; the eliminated chain replays through its definitions: b2 = a + 2 = 2
; CHECK: \( \|b2\|  #x02 \)
(get-value (b2))
; mentioning an eliminated variable re-asserts its equation; b1 = a + 1
; = 1, so requiring b1 distinct from 1 contradicts
(push 1)
(assert (distinct b1 #x01))
; CHECK: ^unsat
(check-sat)
(pop 1)
; a witness-dropped variable is NOT pinned to its replay value: the
; original bound (bvult c2 #x02) returns and allows c2 = 1
(push 1)
(assert (= c2 #x01))
; CHECK: ^sat
(check-sat)
(pop 1)
; but the restored original still binds: c2 = 2 exceeds it
(push 1)
(assert (= c2 #x02))
; CHECK: ^unsat
(check-sat)
(pop 1)
; CHECK: ^sat
(check-sat)
(exit)
