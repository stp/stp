; The rebuild-boundary base pass now includes whole-conjunction
; constant-bit propagation, exactly as the batch pipeline runs it.
; Nothing here is an equality naming a symbol -- equality propagation
; cannot see this base -- but the bit-level pair pins every bit of `a`
; (the AND forces the low nibble, the OR the high nibble), which only
; constant-bit propagation derives. Pins:
;
; 1. The valve rebuild collapses the base and the fixed symbol replays
;    its value for get-value.
; 2. Later content contradicting the derived constant is unsat: the
;    fixing is an implied truth, restored on mention like any harvested
;    equation.
; 3. Content consistent with it stays sat.
; RUN: %solver -s --incremental --incremental-reencode-limit 1 --check-sanity %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --incremental-auto-engage-at 1 --incremental-reencode-limit 1 --check-sanity %s 2>&1 | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun y1 () (_ BitVec 12))
(declare-fun y2 () (_ BitVec 12))
(declare-fun y3 () (_ BitVec 12))
(declare-fun y4 () (_ BitVec 12))
(declare-fun y5 () (_ BitVec 12))
(declare-fun y6 () (_ BitVec 12))
(assert (= (bvand a #x0f) #x0f))
(assert (= (bvor a #x0f) #xff))
; heavy throwaway rounds accumulate dead clause mass -- each a distinct
; multiplier circuit -- until the valve's mass ratio trips
(push 1)
(assert (bvugt (bvmul y1 y1) #x003))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y2 y2) #x003))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y3 y3) #x003))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y4 y4) #x003))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y5 y5) #x003))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y6 y6) #x003))
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
; the bit-level pair fixed every bit: a = 0xff, replayed for the model
; CHECK: \( \|a\|  #xFF \)
(get-value (a))
; contradicting the derived constant is unsat
(push 1)
(assert (distinct a #xff))
; CHECK: ^unsat
(check-sat)
(pop 1)
; consistent content stays sat
(push 1)
(assert (= (bvxor a #xff) #x00))
; CHECK: ^sat
(check-sat)
(pop 1)
; CHECK: ^sat
(check-sat)
(exit)
