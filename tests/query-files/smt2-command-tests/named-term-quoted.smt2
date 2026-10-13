; Quoted labels: any printable characters but | and \ (section 3.1),
; including unbalanced brackets, which no lexer state may count. A simple
; symbol in bars is the same symbol.
; RUN: %solver %s | %OutputCheck %s
(set-option :produce-models true)
(set-option :produce-assignments true)
(set-option :produce-unsat-cores true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (! (= x #x2a) :named |x is 42|))
(assert (= (! (bvadd x #x01) :named |x + 1 (next)|) #x2b))
(assert (! (bvult |x + 1 (next)| #xff) :named |fits; really|))
(assert (! (= x #x2a) :named plain))
(assert (! (= x #x2a) :named |:not-a-keyword|))
(assert (and |plain| |:not-a-keyword| |x is 42|))
; A reserved word in bars is a distinct quoted symbol, as in declare-const.
(assert (! (= x #x2a) :named |assert|))
; CHECK: ^sat$
(check-sat)
; CHECK-L: ((! x :named |(((|) #x2A)
; CHECK-L: (|(((| #x2A)
; CHECK-L: ((bvadd |)| |)|) #x54)
; CHECK-L: (|; not a comment| #x2A)
; CHECK-L: (|"q"| #x2A)
; CHECK-L: (|x + 1 (next)| #x2B)
; CHECK-L: (plain true)
; CHECK-L: (|plain| true)
; CHECK-L: (|assert| true)
(get-value ((! x :named |(((|) |(((| (! x :named |)|) (bvadd |)| |)|) (! x :named |; not a comment|) |; not a comment| (! x :named |"q"|) |"q"| |x + 1 (next)| plain |plain| |assert|))
; CHECK-L: ((|:not-a-keyword| true) (|assert| true) (|fits; really| true) (|plain| true) (|x is 42| true))
(get-assignment)
; Sorts are a separate namespace, so a label's name is free for define-sort.
(define-sort plain () (_ BitVec 8))
(declare-const z plain)
(assert (= z x))
; A let variable may share a label's name; the label is what remains after.
(assert (let ((fresh true)) (and fresh (! (= z #x2a) :named fresh))))
(assert fresh)
; CHECK: ^sat$
(check-sat)
(push 1)
(declare-const w (_ BitVec 8))
(assert (! (= w #x01) :named |first one|))
(assert (! (= w #x02) :named |((|))
; CHECK: ^unsat$
(check-sat)
; CHECK-L: (|first one| |((|)
(get-unsat-core)
(pop 1)
