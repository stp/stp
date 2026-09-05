; REQUIRES: cadical
; An established many-query session initially keeps its useful trail when
; floating point arrives late. Retiring immediately at this boundary used to
; rebuild the array registry and discard the search state accumulated by the
; prefix; representative Vector traces became 2x--6x slower. Late FP is not
; an unconditional exemption, though: if three FP checks leave the solver
; below the established-state floor, the rebuild is cheap and the
; phase-sensitive FP tail wins the trade. Early-FP sessions still retire at
; once (trail-reuse-retired-for-fp.smt2), while growing/refinement-heavy late
; sessions use their independent boundaries.
;
; Six distinct array queries establish the many-solve shape. The seventh adds
; FP while the solver is deliberately tiny. Its first three checks must not
; rebuild; the fourth classifies the state as stalled and retires the trail.
; RUN: %solver --cadical --incremental --incremental-profile --check-sanity %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)
(declare-fun A () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun f () (_ FloatingPoint 8 24))

(push 1)
(assert (= (select A #x01) #x01))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (select A #x02) #x02))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (select A #x03) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (select A #x04) #x04))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (select A #x05) #x05))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (select A #x06) #x06))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.isNaN f))
; CHECK: Incremental profile cbp/backend: check=7 .*rebuild-trail=0
; CHECK: ^sat
(check-sat)
; CHECK: Incremental profile cbp/backend: check=8 .*rebuild-trail=0
; CHECK: ^sat
(check-sat)
; CHECK: Incremental profile cbp/backend: check=9 .*rebuild-trail=0
; CHECK: ^sat
(check-sat)
; CHECK: Incremental profile cbp/backend: check=10 .*rebuild-trail=1
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
