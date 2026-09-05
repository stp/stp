; RUN: %solver %s | %OutputCheck %s
;
; A select from a RoundingMode-element array denotes one of the five modes,
; exactly as a RoundingMode variable does. The 5-bit carrier has 27 further
; patterns; without the solve-time pinning of such reads (FpTotalise), "the
; cell differs from every mode" would be answered sat by giving the cell a
; junk pattern -- the same hole the one-hot constraint on RoundingMode
; variables closes at declaration.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 2) RoundingMode))
(declare-fun i () (_ BitVec 2))
(assert (distinct (select a i) RNE RTP RTN RTZ RNA))
; CHECK: ^unsat
(check-sat)
