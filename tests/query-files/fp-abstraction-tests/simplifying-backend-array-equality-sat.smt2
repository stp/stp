; REQUIRES: minisat
; RUN: %solver -d --fp-abstraction=1 --fp-abstraction-ops=all --simplifying-minisat --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; As simplifying-backend-sat, under an active array equality. The array
; checker reads the model first, so a lemma spliced over an eliminated
; proxy surfaced as "the complete array checker and the
; bit-blasted/model-evaluation path disagree on the same candidate".
(set-logic QF_AUFBVFP)
(declare-const x1 Float16)
(declare-const x6 (Array Float64 Float16))
(declare-const x (Array Float64 Float16))
(declare-fun f ((_ BitVec 1) (_ BitVec 9)) (_ BitVec 3))
(declare-fun p ((_ BitVec 6) (_ BitVec 4) (_ BitVec 14)) Bool)
(assert (or (= x6 x) (ite false false (p (_ bv0 6) ((_ fp.to_sbv 4) RNA ((_ to_fp 8 24) roundNearestTiesToEven (_ bv3 3))) (_ bv0 14))) (distinct (distinct (fp.add roundTowardPositive x1 x1) (select x6 (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)))) (p (_ bv0 6) (_ bv0 4) ((_ zero_extend 11) (f (_ bv0 1) (_ bv0 9)))))))
(check-sat)
