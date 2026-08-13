; The freeze rule: a variable whose bits already reached the SAT solver in
; an earlier check-sat must not have a later defining equation simplified
; away under its own substitution -- the equation has to constrain the
; existing bits. A driver that eliminated it would answer sat here.
; RUN: %solver --incremental %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (bvult y #x10))
; CHECK-NEXT: ^sat
(check-sat)
; y's bits are in the solver now; this equation must really constrain them.
(assert (= y #x20))
; y < 16 and y = 32 together are unsatisfiable.
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
