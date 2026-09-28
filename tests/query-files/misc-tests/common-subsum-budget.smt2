; RUN: %solver -s --common-subsum-budget=10 %s 2>&1 | %OutputCheck %s
; CHECK: BVPLUS applications saved:[0-9]+ Chunks:1 Truncated:1 Tally:0
; CHECK: ^sat
; RUN: %solver -s %s 2>&1 | %OutputCheck --check-prefix=FULL %s
; FULL: BVPLUS applications saved:[0-9]+ Chunks:1 Truncated:0 Tally:[1-9][0-9]*
; FULL: ^sat
; The tally budget bounds what common sub-term extraction may spend. Five
; additions, each a prefix of the next, are the shape a flattened chain of
; gates has; the greedy loop re-nests such a staircase one pair per round,
; repairing every holder each time, which is the cube of the staircase's
; length. Under a budget the tally's build cannot finish within, the build
; is not begun and the pass says so; the co-traveller chunk -- the three
; operands every addition holds -- is still taken, since it costs no tally.
; The answer is the same either way. The bounds are comparisons rather
; than equations, which nothing distributes or solves, and the bvand keeps
; every variable in use twice over, so unconstrained-variable elimination
; cannot peel the staircase away from its last operand before the pass runs.
(set-logic QF_BV)
(declare-const v0 (_ BitVec 20))
(declare-const v1 (_ BitVec 20))
(declare-const v2 (_ BitVec 20))
(declare-const v3 (_ BitVec 20))
(declare-const v4 (_ BitVec 20))
(declare-const v5 (_ BitVec 20))
(declare-const v6 (_ BitVec 20))
(declare-const m3 (_ BitVec 20))
(declare-const m4 (_ BitVec 20))
(declare-const m5 (_ BitVec 20))
(declare-const m6 (_ BitVec 20))
(declare-const m7 (_ BitVec 20))
(assert (bvult (bvadd v0 v1 v2) m3))
(assert (bvult (bvadd v0 v1 v2 v3) m4))
(assert (bvult (bvadd v0 v1 v2 v3 v4) m5))
(assert (bvult (bvadd v0 v1 v2 v3 v4 v5) m6))
(assert (bvult (bvadd v0 v1 v2 v3 v4 v5 v6) m7))
(assert (= (bvand v0 v1 v2 v3 v4 v5 v6 m3 m4 m5 m6 m7) (_ bv1 20)))
(check-sat)
