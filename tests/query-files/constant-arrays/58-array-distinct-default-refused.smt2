; RUN: not %solver --array-equality %s 2>&1 | %OutputCheck %s
; RUN: not %solver --array-equality --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: not %solver --array-equality --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK: constant-array defaults cannot contain UF applications, Real terms or array-equality conditions
; Array DISTINCT would lower to array equalities hidden inside the default,
; so it must be refused through the same recoverable API restriction.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun flags () (Array (_ BitVec 8) Bool))
(assert (= flags ((as const (Array (_ BitVec 8) Bool)) (distinct a b c))))
(check-sat)
