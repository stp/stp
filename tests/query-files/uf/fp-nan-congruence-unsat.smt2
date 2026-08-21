; The whole risk of admitting FloatingPoint, in one query.
;
; SMT-LIB's = on floats is identity of *values*, and there is one NaN value
; with many bit patterns. So x and y below are equal, and congruence requires
; f(x) = f(y). The UF checker buckets applications by the raw bytes of their
; actuals, so two differently-payloaded NaNs land in different buckets, no
; conflict is reported, the candidate is certified, and STP answers sat on a
; formula that is unsat.
;
; This must be unsat. It answers sat if FloatingPoint is merely admitted and
; the equality question left unanswered.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=on --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
(set-logic QF_UFBVFP)
(declare-fun f ((_ FloatingPoint 8 24)) (_ BitVec 4))
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (fp.isNaN y))
(assert (distinct (f x) (f y)))
(check-sat)
