; Section 4.1.6: the labels of a command are defined in left-to-right
; post-order, so a label is usable in any later sibling of the same command
; and in every later command. Every command with a term argument is a site.
; RUN: %solver %s | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
; A label defined in one argument is visible in the next.
(assert (and (! (= x #x2a) :named a) a))
; ite visits its condition first, so both branches may use its label.
(assert (ite (! (= y #x07) :named c) c c))
; A label from the then-branch is visible in the else-branch.
(assert (ite (= x #x2a) (! (= y #x07) :named t) (not t)))
; Labels chain within a command and are visible in later commands.
(assert (= (! x :named inner) (! (bvadd inner #x00) :named outer)))
(assert (= outer #x2a))
; A closed subterm of a define-fun body may be named; the parameter may not
; appear in it. The label is usable afterwards.
(define-fun g ((p (_ BitVec 8))) Bool (and (= p (! x :named cx)) (= p #x2a)))
(define-const d Bool (! (bvult y #x10) :named small))
(assert (and (g x) d small))
; CHECK: ^sat$
(check-sat)
; CHECK-L: (a true)
; CHECK-L: (c true)
; CHECK-L: (t true)
; CHECK-L: (inner #x2A)
; CHECK-L: (outer #x2A)
; CHECK-L: (cx #x2A)
; CHECK-L: (small true)
(get-value (a c t inner outer cx small))
; A label defined inside get-value is usable in the same list and later.
; CHECK-L: ((! (= x #x2a) :named q) true)
; CHECK-L: (q true)
(get-value ((! (= x #x2a) :named q) q))
; CHECK-L: (q true)
(get-value (q))
; check-sat-assuming is a site too.
; CHECK: ^unsat$
(check-sat-assuming ((! (distinct x #x2a) :named r)))
; CHECK: ^unsat$
(check-sat-assuming (r))
; CHECK: ^sat$
(check-sat-assuming ((not r)))
; The labels are definitions, not declarations: none appears in the model.
; CHECK: ^sat$
(check-sat)
; CHECK-NOT: define-fun \|a\|
; CHECK-NOT: define-fun \|inner\|
; CHECK-NOT: define-fun \|q\|
; CHECK: define-fun \|y\|
(get-model)
