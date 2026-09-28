; The ordering rewrite declines a group larger than its carrier can hold.
;
; A sort from (declare-sort S 0) is carried by a bit-vector of --uf-sort-width
; bits and is itself unbounded, so the carrier's capacity is a fact about the
; encoding and not about the query. Where the width really is the sort's own,
; the parser's cardinality fold has already replaced an oversized group with
; false and there is nothing left here to order; where it is a carrier, the
; fold stands down deliberately, and this declines for the same reason rather
; than inheriting it.
;
; The narrow leg used to have no verdict to check. Five elements of an unbounded
; sort are satisfiable and STP answered unsat at a two-bit carrier, so the leg
; asserted nothing rather than pin a wrong answer as expected output. The
; carrier-capacity check now refuses instead, so the leg has an answer again --
; `unknown` -- and it is one the query's own semantics support.
;
; Widen the carrier by one bit and the group fits. Then the answer is the
; query's own, and the leg checks it.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s --uf-sort-width=2 %s 2>&1 | %OutputCheck --check-prefix=TIGHT %s
; RUN: %solver --uninterpreted-functions --incremental=off -s --uf-sort-width=3 %s 2>&1 | %OutputCheck --check-prefix=ROOMY %s
;
; TIGHT-NOT: Ordered
; TIGHT: ^unknown
; TIGHT: DECLARED-SORT-DONE
;
; ROOMY: Ordered 1 symmetric distinct group\(s\)
; ROOMY: ^sat
; ROOMY: DECLARED-SORT-DONE
;
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun e0 () S)
(declare-fun e1 () S)
(declare-fun e2 () S)
(declare-fun e3 () S)
(declare-fun e4 () S)
(assert (distinct e0 e1 e2 e3 e4))
(check-sat)
(echo "DECLARED-SORT-DONE")
