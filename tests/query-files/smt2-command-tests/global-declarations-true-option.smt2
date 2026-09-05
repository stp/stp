; The option itself: it is a boolean whose required default is false (SMT-LIB
; 2.6, section 4.1.7), it can be set in start mode, and get-option must report
; back what was set instead of answering "unsupported".
; RUN: %solver %s | %OutputCheck %s
; CHECK: ^false$
(get-option :global-declarations)
(set-option :global-declarations true)
; CHECK-NEXT: ^true$
(get-option :global-declarations)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
; CHECK-NEXT: ^sat$
(check-sat)
