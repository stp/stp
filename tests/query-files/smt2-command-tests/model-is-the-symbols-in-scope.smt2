; A model names the symbols in scope at the check it answers, and nothing else.
;
; PrintFullCounterExampleSMTLIB2 took its symbols from STPMgr::getSymbols(),
; which is the intern table: every symbol the manager ever made, with no notion
; of a scope. A declaration whose frame was popped is still interned, so when a
; later frame rebound the name the model listed it twice --
;
;   (define-fun |x| () (_ BitVec 4) #xE)
;   (define-fun |x| () Bool false)        <- the popped declaration
;
; -- which is not a model (one name, two values) and cannot be read back.
; RUN: %solver %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK: ^sat$
; The second check's model names x once, at the sort that is in scope there.
; CHECK: \(define-fun \|x\| \(\) \(_ BitVec 4\) #x[0-9A-F]\)
; CHECK-NOT: \(define-fun \|x\| \(\) Bool
(set-option :produce-models true)
(set-option :incremental on)
(set-logic QF_BV)
(push 1)
(declare-fun x () Bool)
(assert (not x))
(check-sat)
(pop 1)
(push 1)
(declare-fun x () (_ BitVec 4))
(assert (distinct x (_ bv15 4)))
(check-sat)
(get-model)
(pop 1)
(exit)
