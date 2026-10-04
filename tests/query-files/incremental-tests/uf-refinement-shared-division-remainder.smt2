; The whole-stack UF block, from the push/pop fuzzing: two remainders over one
; divisor must not be blasted as the same bits. They were, because the memo
; that pairs a BVDIV with the BVMOD of the same operands was keyed by a BVDIV
; the lookup built through the simplifying factory, and (x umod y) / y folds
; to a quotient the dividend does not appear in. The second remainder then
; stood for the first one's dividend, so the SAT model satisfied the block
; while the raw stack refuted it -- no theory owed a lemma for the refutation
; and the round aborted with "UF refinement rejected a candidate without
; retaining a block-scoped lemma". The batch driver reaches the same wall from
; the other side ("refinement reached undecided without a pending
; candidate-blocking lemma"), hence the two engagement arms below: the
; repeated check-sat is what engages the incremental driver when a model is
; asked for, and is answered from the verdict cache when one is not.
;
; RUN: %solver --bb.div-by-mult 1 %s | %OutputCheck %s
; RUN: %solver --bb.div-by-mult 1 -d %s | %OutputCheck %s
; RUN: %solver --bb.div-by-mult 1 --incremental=on %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK: ^sat$
; CHECK: ^sat$
;
; EXPECT: sat, three times -- y = 5 with both applications 1 is a model
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun u () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))
(assert (bvult u v))
(check-sat)
(check-sat)
(push 1)
(assert (= (bvurem (bvurem (f u) y) y) #x01))
(assert (= (bvurem (bvurem (f v) y) y) #x01))
(check-sat)
