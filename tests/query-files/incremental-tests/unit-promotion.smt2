; A pushed level that sits identical at the same depth for eight
; consecutive solves is promoted to permanent unit clauses: its
; assumption disappears and its clauses join root-level preprocessing.
; Pins:
;
; 1. The promotion fires (stats line) and the promoted constraint still
;    binds: content contradicting it is unsat.
; 2. Retracting the promoted level restarts the solver (stats line) and
;    the constraint genuinely retracts: content contradicting the OLD
;    promoted level is sat afterwards -- a stale unit here would be a
;    wrong unsat.
; Promotion only engages once trail reuse is retired (the same session
; split as inprobing retirement): the floating-point conjunct below
; retires the trail from the first solve, exactly like the sessions
; promotion exists for.
; RUN: %solver -s --incremental %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --incremental-auto-engage-at 1 %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun f () (_ FloatingPoint 8 24))
(assert (bvult y #xff))
(assert (fp.gt f (_ +zero 8 24)))
; the stable level: lives at depth 1 through every solve below
(push 1)
(assert (bvult x #x10))
; nine churning rounds on top; the stable level promotes at the ninth
(push 1)
(assert (bvugt y #x00))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x01))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x02))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x04))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x05))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x06))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x07))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x08))
; CHECK: promoted level 1
; CHECK: ^sat
(check-sat)
(pop 1)
; the promoted constraint still binds
(push 1)
(assert (bvugt x #x20))
; CHECK: ^unsat
(check-sat)
(pop 1)
; retract the promoted level: the solver must restart and the old
; bound must genuinely stop binding
(pop 1)
(push 1)
(assert (bvugt x #x20))
(push 1)
(assert (bvugt y #x09))
; CHECK: promoted prefix retracted
; CHECK: ^sat
(check-sat)
(pop 1)
(pop 1)
(exit)
