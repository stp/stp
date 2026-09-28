; A sort introduced by declare-sort must never be read as having as many
; values as its carrier has patterns.
;
; The carrier is a bit-vector of --uf-sort-width, chosen so the encoding can
; tell apart more elements than a query can name; but the SORT is unbounded,
; so (distinct s0 ... s16) is satisfiable in a seventeen-element domain no
; matter how narrow the carrier is. Reading the width as a cardinality answers
; that unsat -- a wrong answer where the alternative is merely a slow one --
; so a width any declared sort has claimed is never guarded, and a genuine
; bit-vector of that same width stops being guarded too rather than have the
; two be told apart by something that cannot tell them apart.
;
; Seventeen elements at the default width: satisfiable, and it must stay so.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: REACHED-END
;
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-const s0 S)
(declare-const s1 S)
(declare-const s2 S)
(declare-const s3 S)
(declare-const s4 S)
(declare-const s5 S)
(declare-const s6 S)
(declare-const s7 S)
(declare-const s8 S)
(declare-const s9 S)
(declare-const s10 S)
(declare-const s11 S)
(declare-const s12 S)
(declare-const s13 S)
(declare-const s14 S)
(declare-const s15 S)
(declare-const s16 S)
(assert (distinct s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16))
(check-sat)
(echo "REACHED-END")
