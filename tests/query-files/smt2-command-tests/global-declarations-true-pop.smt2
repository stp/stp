; With :global-declarations true, declarations and definitions are permanent
; rather than being added to the assertion stack (SMT-LIB 2.6, section 4.1.5), so
; a name declared inside an assertion level is still in scope after the pop.
; RUN: %solver %s | %OutputCheck %s
(set-option :global-declarations true)
(set-logic QF_BV)
(push 1)
(declare-fun x () (_ BitVec 4))
(pop 1)
(assert (= x #x1))
; CHECK: ^sat$
(check-sat)
