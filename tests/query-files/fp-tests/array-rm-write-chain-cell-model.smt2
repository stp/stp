; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality -r %s | %OutputCheck %s
; RUN: %solver --incremental=on --array-equality %s | %OutputCheck %s
; RUN: %solver --incremental=on --array-equality -r %s | %OutputCheck %s
;
; The model half of array-rm-write-chain-cell-is-a-mode.smt2, and the control
; that pinning the cell is not the same as publishing a default for it.
;
; Four of the five modes are excluded from a[i] by four disequalities between
; a chain of one write and its own base, which the array-equality context
; rewrites into constraints on that cell rather than abstracting them. The
; cell is a read minted after the pinning pass ran, so a free carrier could
; satisfy all four at once by naming no mode -- and get-value then published
; the carrier itself, a raw five-bit pattern where a mode name belongs:
;
;   ( (select |a| |i|)  #b11000 )
;
; a value of no RoundingMode, and a different one on each route (#b11000 on
; the batch routes of one build, #b01001 on the incremental ones), because
; nothing constrained it. The congruence axioms compare the carriers the
; solve decided; model evaluation compares what those bits are taken to mean.
;
; RNA is the only mode the four leave, and it is the answer whether or not any
; cell needed completing: a fix that pinned the cell but published a
; completion for it instead of the value the solve decided would fail here.
;
; CHECK: ^sat
; CHECK: ^\( \(select \|a\| \|i\|\) RNA \)$
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-fun a () (Array RoundingMode RoundingMode))
(declare-fun i () RoundingMode)
(assert (not (= (store a i RNE) a)))
(assert (not (= (store a i RTP) a)))
(assert (not (= (store a i RTN) a)))
(assert (not (= (store a i RTZ) a)))
(check-sat)
(get-value ((select a i)))
(exit)
