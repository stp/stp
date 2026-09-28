; --uf-sort-width is bounded, because both ends were reachable and neither end
; failed cleanly.
;
; Zero made every element of a declared sort a zero-width term, which the legacy
; width checks read as a Boolean: an abort inside a header on an asserting build,
; and otherwise a query answered and a model printed at the wrong sort. The top
; end overflows the word arithmetic the bit-vector layer is built on -- at
; 4294967233 two elements of an unbounded sort answered unsat -- and the widths
; below that crashed with no diagnostic at all rather than erroring.
;
; The ceiling is far above any carrier a query can exhaust, so the range costs
; nothing a caller can want: 1024 bits tells apart more elements than a query
; can name.
;
; RUN: not %solver --uninterpreted-functions --uf-sort-width=0 %s 2>&1 | %OutputCheck --check-prefix=REJECT %s
; RUN: not %solver --uninterpreted-functions --uf-sort-width=1025 %s 2>&1 | %OutputCheck --check-prefix=REJECT %s
; RUN: not %solver --uninterpreted-functions --uf-sort-width=4294967295 %s 2>&1 | %OutputCheck --check-prefix=REJECT %s
; RUN: %solver --uninterpreted-functions --uf-sort-width=1024 %s 2>&1 | %OutputCheck --check-prefix=ACCEPT %s
; RUN: %solver --uninterpreted-functions --uf-sort-width=1 %s 2>&1 | %OutputCheck --check-prefix=ACCEPT %s
;
; REJECT: --uf-sort-width
; REJECT-NOT: ^sat
;
; ACCEPT: ^sat
;
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun e0 () S)
(declare-fun e1 () S)
(assert (= e0 e1))
(check-sat)
