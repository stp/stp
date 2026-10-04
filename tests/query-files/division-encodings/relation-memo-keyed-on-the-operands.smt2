; BVDIV and BVMOD of one operand pair share the relation's fresh quotient and
; remainder, and the blaster's memo decides which terms are one pair. Keying
; it by a BVDIV built for the lookup made unrelated terms share a pair: the
; term factory simplifies, and two of its quotient rules return a node the
; dividend does not appear in. The second term blasted then took the first's
; remainder, with no relation over its own dividend -- the same bits for both,
; so each query below came back unsat.
;
; The first query folds (x umod y) / y, which drops the dividend whatever the
; divisor is. The second folds x / 0b111111 to a constant, because the
; dividend's leading zeros settle the comparison the rule leaves behind; that
; is the constant-divisor arm of the relational encoding, and it needs the
; simplifier out of the way only because the simplifier would otherwise fold
; a remainder smaller than its divisor before the blaster sees one.
;
; RUN: %solver --bb.div-by-mult 1 %s | %OutputCheck %s
; RUN: %solver --bb.div-by-mult 1 --bb.div-lemmas 1 %s | %OutputCheck %s
; RUN: %solver --bb.div-by-mult 1 --incremental=on %s | %OutputCheck %s
; RUN: %solver --bb.div-by-const-width=6 --disable-simplifications %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK: ^sat$
;
; EXPECT: sat twice -- x1 = 1, x2 = 2, y = 5 and a = 1, b = 2 are models
(set-logic QF_BV)
(declare-fun y () (_ BitVec 8))
(declare-fun x1 () (_ BitVec 8))
(declare-fun x2 () (_ BitVec 8))
(declare-fun a () (_ BitVec 5))
(declare-fun b () (_ BitVec 5))
(push 1)
(assert (not (= (bvurem (bvurem x1 y) y) (bvurem (bvurem x2 y) y))))
(check-sat)
(pop 1)
(push 1)
(assert (= (bvurem (concat #b0 a) #b111111) (_ bv1 6)))
(assert (= (bvurem (concat #b0 b) #b111111) (_ bv2 6)))
(check-sat)
(pop 1)
