; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; A rounding mode is carried as a 5-bit bitvector, and every operation that
; takes one used to check exactly that: "is it 5 bits wide". SMT-LIB's
; RoundingMode has five values; the carrier has thirty-two.
;
; The other twenty-seven are not an error deep in symfpu -- roundingDecision
; is a chain of equalities against the five modes, and with all of them false
; it falls through to truncate, overflowing to the maximum and underflowing to
; the smallest subnormal. That is a sixth mode, in no standard. This input
; pins r away from all five and was answered sat, having computed under it.
;
; The check is now the sort, not the width: STPMgr::isRoundingModeSortedTerm.
; CHECK: expected a rounding mode
(set-logic QF_BVFP)
(declare-const r (_ BitVec 5))
(declare-const x (_ FloatingPoint 8 24))
(assert (distinct r #b00001)) (assert (distinct r #b00010))
(assert (distinct r #b00100)) (assert (distinct r #b01000))
(assert (distinct r #b10000))
(assert (fp.isNormal (fp.add r x x)))
(check-sat)
