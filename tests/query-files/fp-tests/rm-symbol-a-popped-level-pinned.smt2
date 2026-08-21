; RUN: %solver --incremental=on %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; A RoundingMode value a model hands back names one of the five modes, even
; where the solve that named the term has been popped.
;
; A mode is carried in five bits, one-hot, so twenty-seven of the thirty-two
; patterns name nothing. Every mode a formula names is pinned to the five --
; here by the declaration of r -- but that pin belongs to the level it was
; made at, and the incremental encoding keeps r's SAT variables after the
; level is popped, on purpose. The second check-sat names r nowhere, so its
; bits are free and the backend leaves whatever it likes in them: get-value
; printed the carrier, ( |r|  #b01010 ), which is not a term of the sort and
; names no mode. Through the programmatic model API the same value aborted
; the process.
;
; A RoundingMode the model records nothing for has always been completed with
; RNE, and free bits are owed the same answer. Matched against the five names
; rather than against RNE alone: the fix decides what a free carrier completes
; to, not what the backend leaves in it, and a run whose bits happened to name
; a mode already would otherwise fail for no reason.
(set-logic QF_FP)
(set-option :produce-models true)
(set-option :global-declarations true)
(push 1)
(declare-fun c () Bool)
(declare-fun r () RoundingMode)
(assert (fp.gt (fp.roundToIntegral r (_ -oo 11 53))
               (fp.sub (ite c RTN r)
                       (fp.roundToIntegral r (_ -oo 11 53))
                       (fp.roundToIntegral r (_ -oo 11 53)))))
; CHECK: ^unsat
(check-sat)
(pop 1)
; CHECK: ^sat
(check-sat)
; CHECK: ^\( \|r\| (RNE|RNA|RTP|RTN|RTZ) \)$
(get-value (r))
