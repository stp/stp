; reset-assertions is defined in terms of the same option (SMT-LIB 2.6, section
; 4.2.4): with :global-declarations false it removes the base-level declarations
; and definitions along with the assertions, so afterwards the name is unknown.
; reset-assertions-drops-declarations covers the redeclaration side of this;
; here the popped name is used rather than redeclared.
; RUN: not %solver %s | %OutputCheck %s
(set-option :global-declarations false)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(define-fun y () (_ BitVec 4) (bvnot x))
(assert (= x #x1))
; CHECK: ^sat$
(check-sat)
(reset-assertions)
; CHECK: .*error.*token: y.*
(assert (= y #xE))
(check-sat)
