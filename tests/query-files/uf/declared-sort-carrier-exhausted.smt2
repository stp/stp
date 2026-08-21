; A carrier that cannot hold the terms the query names of its sort gets no
; answer, and says which sort ran out.
;
; A sort declared by declare-sort is unbounded; its carrier is not. So a query
; naming more terms of one sort than the carrier can tell apart may be
; unsatisfiable in the encoding while being satisfiable in the theory. Only
; unsat can be wrong that way -- every carrier pattern denotes an element and
; bit equality on the carrier is the sort's equality, so any satisfying carrier
; assignment is a genuine model -- and an unsound unsat is the one answer a
; caller cannot tell from a real refutation. Neither verdict is reportable, so
; neither is reported.
;
; Five elements over a two-bit carrier used to answer unsat in a hundredth of a
; second, and this suite pinned that as expected output. Widen the carrier by
; one bit and the query fits, and then the answer is the query's own.
;
; The reason is where the actionable part lives: `incomplete` is SMT-LIB's own
; word for it, and the sentence beside it names the sort, the count, the width
; and what to raise -- a WIDTH, which is the correction this row records. It
; first said "raise to at least 5" for five elements, four times larger than
; needed, and above 1024 named a value the flag's own range check refuses.
;
; The query is solved rather than refused, and only an unsat is withheld: every
; carrier assignment denotes a real assignment of elements, so a sat found over
; a narrow carrier is a genuine answer and is kept.
;
; RUN: %solver --uninterpreted-functions --incremental=off --uf-sort-width=2 %s 2>&1 | %OutputCheck --check-prefix=TIGHT %s
; RUN: %solver --uninterpreted-functions --incremental=on  --uf-sort-width=2 %s 2>&1 | %OutputCheck --check-prefix=TIGHT %s
; RUN: %solver --uninterpreted-functions --incremental=off --uf-sort-width=3 %s 2>&1 | %OutputCheck --check-prefix=ROOMY %s
; RUN: %solver --uninterpreted-functions --incremental=on  --uf-sort-width=3 %s 2>&1 | %OutputCheck --check-prefix=ROOMY %s
;
; TIGHT-NOT: ^unsat
; TIGHT: ^unknown
; TIGHT: :reason-unknown \(incomplete "the query needs up to 5 elements of sort S, and --uf-sort-width=2 tells only 4 apart; raise --uf-sort-width to at least 3"\)
;
; ROOMY: ^sat
; ROOMY: :reason-unknown \(error "the last answer was not unknown"\)
;
; TIGHT: WITHHELD-DONE
; TIGHT: ^sat
; ROOMY: WITHHELD-DONE
; ROOMY: ^sat
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
(get-info :reason-unknown)
(echo "WITHHELD-DONE")
; A satisfiable query over the same narrow carrier keeps its answer: it is
; sound whatever the carrier's width, and refusing it was a plain loss.
(reset)
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun e0 () S)
(declare-fun e1 () S)
(declare-fun e2 () S)
(declare-fun e3 () S)
(declare-fun e4 () S)
(assert (= e0 e1))
(assert (= e2 e3))
(assert (= e3 e4))
(check-sat)
