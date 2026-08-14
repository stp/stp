; RUN: %solver -d --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; Every array equality here is a chain of writes against a base of its
; own chain, so lowering solves all six by rewriting: no abstraction
; variable, no record, and no consistency checker behind any of them.
; They also sit in the untaken branch of an if-then-else whose condition
; is asserted, so preprocessing deletes them and the solver constrains
; none of the arrays -- yet the lowerings still answer an equality
; handle, and the counterexample check compares each one against the
; contents the model publishes for its operands.
;
; That comparison only means anything if both sides complete an
; unobserved cell identically. RoundingMode is a one-hot encoding, so
; all-zero denotes no mode at all and the printer publishes RNE for such
; a cell; evaluating a lowering's reads has to say RNE too. It used to
; say all-zero bits in the checker's contents walk while the read
; evaluator said RNE, and this query died in the check on both
; polarities of the disagreement. Found by murxla.
;
; The pinned line is the point: the constant array underneath the
; observed cells is a real mode, and it is the same value every other
; reader completes with. Only that base is pinned: which cell the store
; names, and what it holds, is whatever the SAT solver happened to pick
; for _x1 and _x6 -- minisat says RNE and cadical says RNA, and both are
; models. Pinning them said nothing about the completion this test is
; about, and only made the test solver-specific.
; CHECK-L: (define-fun |_x5| () (Array RoundingMode RoundingMode) (store ((as const (Array RoundingMode RoundingMode)) RNE)
(set-logic QF_ABVFP)
(declare-const _x1 RoundingMode)
(declare-const _x2 Bool)
(declare-const _x5 (Array RoundingMode RoundingMode))
(declare-const _x6 RoundingMode)
(declare-const _x8 RoundingMode)
(declare-const _x9 RoundingMode)
(assert _x2)
(assert (not (ite _x2 (= _x8 _x9)
  (distinct (store (store _x5 RTN RTN) _x6 _x1)
            _x5
            (store _x5 RTN RTN)
            (store (store (store (store (store _x5 RTN RTN) _x6 _x1)
                          RTN _x1) (select _x5 _x1) RTN) _x1 RTN)))))
(check-sat)
(get-model)
