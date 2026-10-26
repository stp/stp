; (_ repeat k) whose width passes 2^32 - 1: 65537 * 65537 bits wrapped to
; 131073, and each wrapped concat agreed with itself, so the ill-sorted
; equality below was accepted and answered.

; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "syntax error: line [0-9]+ a bit-vector is at most 4294967295 bits wide

(set-logic QF_BV)
(declare-fun x () (_ BitVec 65537))
(declare-fun z () (_ BitVec 131073))
(assert (= ((_ repeat 65537) x) z))
(check-sat)
