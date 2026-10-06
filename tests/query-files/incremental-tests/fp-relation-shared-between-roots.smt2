; RUN: %solver --incremental=on --max-num-confl=1000 %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at=1 --max-num-confl=1000 %s | %OutputCheck %s
; RUN: %solver --incremental=on --bb.fp-native-div=1 --max-num-confl=1000 %s | %OutputCheck %s
;
; Two relations over the same vectors define the same quotient, so a root
; that builds an earlier root's vectors again takes that root's pair.
;
; fp.rem, fp.sqrt and, under --bb.fp-native-div, fp.div are encoded through a
; defining relation over a fresh quotient and remainder. The incremental
; driver blasts every conjunct as a root of its own, and the floating-point
; term memos start afresh under each, so a term two conjuncts share came
; back with one pair per conjunct, each defined by its own copy of the
; relation. The copies agree on every input, but nothing told the search so:
; to refute two facts about one term it had to prove two dividers
; equivalent. Each query below is refuted with a handful of conflicts once
; the pair is shared; with a pair per conjunct a hundred thousand were not
; enough, and without the budget each ran for minutes.
;
; The first query is a Murxla campaign find, reduced: a remainder that is
; negative cannot have a positive minimum with anything. Its exact cross-check
; lane timed out where the abstracting lane answered at once.
(set-logic QF_FP)
(declare-fun x () Float32)
(declare-fun y () Float32)
(declare-fun c () Float32)
(push 1)
(assert (fp.isNegative (fp.rem x y)))
(assert (fp.isPositive (fp.min (fp.rem x y) x)))
; CHECK: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt (fp.sqrt RNE x) c))
(assert (fp.geq (fp.sqrt RNE x) c))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt (fp.div RNE x y) c))
(assert (fp.geq (fp.div RNE x y) c))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(exit)
