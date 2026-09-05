; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK-L: STP cannot decide equality between whole array terms without --array-equality
; Without --array-equality an equality between whole array terms is
; refused, at the point it is built rather than at the solve.
;
; It used to be a warning, and the solve continued. That was not safe:
; nothing removes the array-sorted operands, so the atom reached the
; solver unconstrained and the verdict could be wrong -- see test 53,
; which answered sat on an unsatisfiable query. A debug build did not
; get that far, aborting on an assertion that the array transform had
; removed every array operation.
;
; Refusing at construction means it does not matter where the equality
; sits: both of these are under a true disjunct and could never affect
; the verdict, and both are still refused. That is deliberate -- the
; option decides whether an opaque equality may be constructed, and the
; Python binding already refuses at that boundary. Abstraction itself is
; deferred until a completed query reaches the solver.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun x () (_ BitVec 2))
(assert (or true (= a b)))
(assert (or true (= b a)))
(assert (= x #b01))
(check-sat)
