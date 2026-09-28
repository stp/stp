; The extensionality encoding creates one fresh index and two fresh element
; terms per array equality. Account for those implicit terms before trusting
; an unsat result over a deliberately tiny declared-sort carrier.
;
; RUN: %solver --incremental=off --uf-sort-width=1 %s 2>&1 | %OutputCheck --check-prefix=TIGHT %s
; RUN: %solver --incremental=on  --uf-sort-width=1 %s 2>&1 | %OutputCheck --check-prefix=TIGHT %s
; RUN: %solver --incremental=off --uf-sort-width=2 %s 2>&1 | %OutputCheck --check-prefix=ROOMY %s
; RUN: %solver --incremental=on  --uf-sort-width=2 %s 2>&1 | %OutputCheck --check-prefix=ROOMY %s
; TIGHT-NOT: ^unsat
; TIGHT: ^unknown
; TIGHT: the query needs up to 3 elements of sort Index, and --uf-sort-width=1 tells only 2 apart
; ROOMY: ^unsat
;
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(assert (distinct i j))
(assert (= a b))
(assert (not (= (select a i) (select b i))))
(check-sat)
(get-info :reason-unknown)
