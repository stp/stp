; Only a closed term may be named. A let variable bound outside the
; annotation makes the term open, even when it shadows a declared constant;
; a let inside the annotation that shadows an outer one keeps it closed.
; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const p Bool)
(assert (let ((p true)) (! (let ((p (= x #x01))) p) :named closed)))
(define-fun g ((a Bool)) Bool (! (let ((a (= x #x01))) a) :named closed-too))
; CHECK: ^\(error "syntax error.*:named requires a closed term.*"\)$
(assert (let ((p true)) (! p :named open)))
(check-sat)
