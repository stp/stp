; set-info accepts any keyword, with or without a value, not just the handful
; the lexer gives a dedicated token to.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :status sat)
(set-info :source "a source")
(set-info :category "crafted")
(set-info :smt-lib-version 2.6)
(set-info :license "MIT")
(set-info :difficulty 5)
(set-info :notes "free-form notes")
(set-info :notes)
(set-info :some-solver-specific-keyword "value")
(set-info :another-one 42)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
; CHECK-NEXT: ^sat
(check-sat)
