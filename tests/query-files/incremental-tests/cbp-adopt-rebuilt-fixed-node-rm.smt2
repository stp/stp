; The RoundingMode face of cbp-adopt-rebuilt-fixed-node.smt2, kept as
; murxla minimised it (including the duplicated assertion): the chained
; equality's definer folds out under the pushed-definition context, the
; adoption's substitution rebuilds the CBP-fixed inner AND, and the
; whole (= (ite ...) _x12 _x8) constraint used to leave the encoding
; with no pinning fact -- the returned model said _x0 = _x2 yet gave
; _x12 and _x8 a value other than the ite's RNE.  --check-sanity
; validates the model against the raw stack.
; RUN: %solver --incremental --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental --incremental-cbp-reset --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --check-sanity %s | %OutputCheck %s
(set-logic QF_FP)
(declare-const _x0 RoundingMode)
(declare-const _x2 RoundingMode)
(declare-const _x7 RoundingMode)
(declare-const _x8 RoundingMode)
(declare-const _x12 RoundingMode)
(push 1)
(assert (= (ite (distinct _x0 _x2) RNA roundNearestTiesToEven) _x12 _x8))
(assert (= (ite (distinct _x0 _x2) RNA roundNearestTiesToEven) _x12 _x8))
(assert (distinct _x0 _x7))
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
