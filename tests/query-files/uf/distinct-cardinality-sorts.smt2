; The cardinality guard on distinct must not fire on a sort whose value count
; is not its carrier's.
;
; An uninterpreted sort is unbounded: however many elements a query asks to be
; pairwise distinct, that is satisfiable. It reaches the guard as the
; bit-vector carrier --uf-sort-width gave it, whose width is chosen to exceed
; any term count a query can have, so the guard never fires on one in practice
; and the answer stays satisfiable.
;
; A floating-point sort's equality identifies values its carrier keeps apart,
; so its count is not 2^width either, and the guard leaves it alone.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK-NEXT: ^sat
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(declare-sort S 0)
(declare-const s0 S)
(declare-const s1 S)
(declare-const s2 S)
(declare-const s3 S)
(declare-const s4 S)
(assert (distinct s0 s1 s2 s3 s4))
(check-sat)
(reset)

(set-logic QF_FP)
(declare-const f0 (_ FloatingPoint 3 3))
(declare-const f1 (_ FloatingPoint 3 3))
(declare-const f2 (_ FloatingPoint 3 3))
(assert (distinct f0 f1 f2))
(check-sat)
(echo "REACHED-END")
