; The extensionality checker reports what its rounds looked like, not just
; how many lemmas it emitted.
;
; The checker deliberately keeps collecting after the first conflict a fixed
; point finds, so a round has no upper bound. That is a good trade when the
; large rounds come first and knock out whole classes of collision at once,
; and a bad one when every round is large -- and a total, or a mean, cannot
; tell those two apart. Until this line existed neither number was printed
; anywhere, so whether to cap a round was not a question anyone could answer
; from evidence.
;
; Five arrays over (Array (_ BitVec 2) (_ BitVec 2)) asserted pairwise
; distinct. The array sort has 256 inhabitants, so this is satisfiable with
; room to spare, but the first candidate model collapses arrays together and
; several rounds of lemmas are needed to separate them: the first query
; measures 3 rounds / 10 lemmas in batch and 5 / 17 in the driver, largest
; round 6 on both. Those figures are search-dependent -- a MiniSat build
; picks different candidates and reports 5 / 11 for the driver -- so what the
; CHECKs pin is the line and its four fields, not the values.
;
; The second query is the reason the report sits at both of TopLevelSTPAux's
; decision exits rather than only at the refinement loop's. It is a
; propositional contradiction, so it is decided before the loop is ever
; entered -- but the counters are cumulative over the checker's lifetime, so
; the first query's rounds are still there to report. Reporting only at the
; loop's exit dropped the line for exactly this query in batch, while the
; driver printed it.
;
; RUN: %solver -s --array-equality --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --array-equality --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: Array equality: [0-9]+ lemmas, [0-9]+ rounds, largest [0-9]+, [0-9]+ atoms folded
; CHECK: ^sat
; CHECK: Array equality: [0-9]+ lemmas, [0-9]+ rounds, largest [0-9]+, [0-9]+ atoms folded
; CHECK: ^unsat
;
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun c () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun d () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun e () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun p () Bool)
(assert (distinct a b c d e))
(check-sat)
(push 1)
(assert (and p (not p)))
(check-sat)
