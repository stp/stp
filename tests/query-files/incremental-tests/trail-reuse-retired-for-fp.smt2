; Trail reuse is retired for floating-point sessions: the FP families
; are phase-sensitive, and a full campaign measured the kept trail
; swinging individual files up to 20x in BOTH directions -- luck, not
; structure -- while the wins it exists for (many small bit-vector
; queries) are FP-free. The backend accepts the option only in its
; configuration window, so retirement restarts the solver without it;
; with FP present from the first solve, as here, nothing has been
; encoded yet and the restart is free. The --stats line below is that
; retirement.
; RUN: %solver -s --incremental %s 2>&1 | %OutputCheck %s
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 24))
(push 1)
(assert (fp.gt a ((_ to_fp 8 24) #x3f800000)))
; CHECK: trail reuse retired
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.isNaN a))
; CHECK: ^sat
(check-sat)
(pop 1)
