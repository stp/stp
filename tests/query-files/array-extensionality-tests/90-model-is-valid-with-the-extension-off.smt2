; The model surface cannot depend on --array-equality. With the extension off
; there used to be a second output path, which printed an array as one line per
; observed read:
;
;   (define-fun |a| (_ BitVec 2) (_ BitVec 8) #b01 #x00)
;
; -- not SMT-LIB, and unreadable by anything. The set-option here is what
; reaches it from inside a file: `auto` resolves to false on QF_ABV, which
; logic_selects_array_equality does not list, so this is the default behaviour
; and not an opt-in.
;
; What must come back is one nullary define-fun whose body is a constant array
; with the observed cell stored over it.
; RUN: %solver %s | %OutputCheck %s
; One line, so one directive: OutputCheck's CHECK directives are ordered by
; line, and a second one looking for `store` would be looking after it.
; CHECK: ^sat$
; CHECK: ^\(define-fun \|a\| \(\) \(Array \(_ BitVec 2\) \(_ BitVec 8\)\) \(store \(\(as const \(Array \(_ BitVec 2\) \(_ BitVec 8\)\)\) #x00\) #b01 #x07\)\)$
; CHECK-NOT: define-fun \|a\| \(_ BitVec
(set-option :produce-models true)
(set-logic QF_ABV)
(set-option :array-equality off)
(declare-fun v () (_ BitVec 8))
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 8)))
(assert (= (select a (_ bv1 2)) v))
(assert (= v (_ bv7 8)))
(check-sat)
(get-model)
(exit)
