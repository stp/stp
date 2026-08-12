; (reset) starts a new session, so it must also clear the fact that the old
; one had become incremental.
;
; A push turns the session incremental. That state used to be written into
; the user flags, where reset() -- which re-derives the frontend's state from
; those same flags -- read it back as though --incremental had been passed on
; the command line. The whole post-reset session then ran through the driver
; from its first solve, taking the forced-first-solve policies with it, on a
; file that never asked for any of that.
;
; A single solve after the reset must be a batch solve, so the driver prints
; nothing at all.
; RUN: %solver --SMTLIB2 -s %s 2>&1 | %OutputCheck %s
; CHECK-NOT: ^Incremental:
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(push 1)
(assert (bvult x #x10))
(check-sat)
(pop 1)
(reset)
(set-logic QF_BV)
(declare-fun y () (_ BitVec 8))
(assert (bvult y #x10))
(check-sat)
(exit)
