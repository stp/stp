; BVDIV and BVMOD of one operand pair share the relation's fresh quotient and
; remainder, and the blaster's memo decides which terms are one pair. Keying
; it by a BVDIV built for the lookup made two unrelated terms share a pair:
; the factory simplifies, and (x umod y) / y folds to a quotient that mentions
; the divisor alone, so every remainder-of-a-remainder over y keyed to the
; same node. The second one blasted took the first's remainder, with no
; relation over its own dividend, and the two were the same bits -- the
; disequality below came back unsat.
;
; RUN: %solver --bb.div-by-mult 1 %s | %OutputCheck %s
; RUN: %solver --bb.div-by-mult 1 --bb.div-lemmas 1 %s | %OutputCheck %s
; RUN: %solver --bb.div-by-mult 1 --incremental=on %s | %OutputCheck %s
; CHECK: ^sat$
;
; EXPECT: sat -- x1 = 1, x2 = 2, y = 5 is a model
(set-logic QF_BV)
(declare-fun y () (_ BitVec 8))
(declare-fun x1 () (_ BitVec 8))
(declare-fun x2 () (_ BitVec 8))
(assert (not (= (bvurem (bvurem x1 y) y) (bvurem (bvurem x2 y) y))))
(check-sat)
