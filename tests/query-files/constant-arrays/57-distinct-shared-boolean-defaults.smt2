; RUN: %solver --array-equality --check-sanity %s | %OutputCheck %s
; RUN: %solver --array-equality --check-sanity --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --check-sanity --incremental=off %s | %OutputCheck %s
; One DISTINCT is shared by a visible positive occurrence and the positive
; and negative defaults of Boolean arrays, whose defaults use packed cells.
; Assumptions must observe the original predicate at both truth values.
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun yes () (Array (_ BitVec 8) Bool))
(declare-fun no () (Array (_ BitVec 8) Bool))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(declare-fun gate () Bool)
(declare-fun positive () Bool)
(declare-fun negative () Bool)
(define-fun d () Bool (distinct x y z))
(assert (or d gate))
(assert (= yes ((as const (Array (_ BitVec 8) Bool)) d)))
(assert (= no ((as const (Array (_ BitVec 8) Bool)) (not d))))
(assert (= positive (select yes #x00)))
(assert (= negative (select no #x00)))
; CHECK: ^unsat$
(check-sat-assuming (positive negative))
; CHECK: ^sat$
(check-sat-assuming (positive))
; CHECK: true
(get-value (d))
; CHECK: false
(get-value ((select no #xff)))
; CHECK: ^sat$
(check-sat-assuming (negative))
; CHECK: false
(get-value (d))
; CHECK: true
(get-value ((select no #xff)))
(push 1)
(assert d)
; CHECK: ^unsat$
(check-sat-assuming (negative))
(pop 1)
; CHECK: ^sat$
(check-sat-assuming (negative))
