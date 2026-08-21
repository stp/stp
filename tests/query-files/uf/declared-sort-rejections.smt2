; A declared sort is not its carrier, and every position that takes a sort says
; so.
;
; All eight of these answered `sat` before the sort had an identity, because a
; declared sort WAS the bit-vector that carries it and so was every other
; declared sort. None of the guards below was at fault: each compares a full
; SourceSort and each already refused a float of the same packed width. They
; were being asked a question that had been answered against the carrier.
;
; They abort rather than reporting a recoverable error, which is the same thing
; the identical guards do for a float in the same position, and is a deliberate
; decision recorded in UF-DECLARED-SORT-DESIGN.md: an input that relied on the
; laxity stops at the offending command rather than continuing with a term
; whose sort nothing can state.
;
; One block per position because each aborts, so each needs its own run. The
; last two are the pair that matter most: an array's index and element sorts
; are where the comment at the C API's array builder says a raw index alongside
; canonicalised ones would break the array's congruence.
;
; RUN: not %solver --uninterpreted-functions %S/Inputs/declared-sort-reject-eq.smt2 2>&1 | %OutputCheck --check-prefix=SORTS %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/declared-sort-reject-eq-bv.smt2 2>&1 | %OutputCheck --check-prefix=SORTS %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/declared-sort-reject-distinct.smt2 2>&1 | %OutputCheck --check-prefix=SORTS %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/declared-sort-reject-bvop.smt2 2>&1 | %OutputCheck --check-prefix=BVOP %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/declared-sort-reject-extract.smt2 2>&1 | %OutputCheck --check-prefix=BVOP %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/declared-sort-reject-ite.smt2 2>&1 | %OutputCheck --check-prefix=ITE %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/declared-sort-reject-select.smt2 2>&1 | %OutputCheck --check-prefix=INDEX %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/declared-sort-reject-store.smt2 2>&1 | %OutputCheck --check-prefix=ELEMENT %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/declared-sort-reject-definefun.smt2 2>&1 | %OutputCheck --check-prefix=DEFINEFUN %s
;
; SORTS: operands of the same sort
; SORTS-NOT: ^sat
;
; BVOP: bitvector operator requires bitvector operands
; BVOP-NOT: ^sat
;
; ITE: ite branches must have the same sort
; ITE-NOT: ^sat
;
; INDEX: array index is not of the declared
; INDEX-NOT: ^sat
;
; ELEMENT: stored value is not of the declared
; ELEMENT-NOT: ^sat
;
; DEFINEFUN: the body's sort does not match
; DEFINEFUN-NOT: ^sat
;
; This file is only the directive carrier; each case is its own input under
; Inputs/ because an abort ends the run.
(set-logic QF_UFBV)
(check-sat)
