; A reason-unknown belongs to the session that produced it.
;
; `reset` and `reset-assertions` both start a session over -- the second back
; at the state `set-logic` left, the first back at the state the solver
; started in -- so a reason recorded before either of them explains a
; check-sat that no longer exists. Left in place it would be handed to whoever
; asked next, and (get-info :reason-unknown) would answer for a query the
; caller had already thrown away.
;
; Both commands are exercised in one file rather than two, and in that order:
; the unknown is re-established between them, so the second half proves
; `reset` clears a reason of its own rather than reading the one
; `reset-assertions` had already cleared. The symbols are re-declared after
; `reset-assertions` because it discards declarations along with assertions.
;
; Both drivers, because they tear down differently -- `reset` drops the
; incremental solver whole, while the batch path has only its tables to clear
; -- and the answer must not depend on which one ran.
;
; A zero-second budget, so no leg turns on the machine being slow enough: a
; deadline of now has already passed by the time the solver is entered. The
; query is a real factorisation, zero-extended so the product cannot wrap --
; modular multiplication would make it trivially satisfiable and no budget
; would bind.
;
; RUN: %solver --incremental=off --max-time=0 %s | %OutputCheck %s
; RUN: %solver --incremental=on --max-time=0 %s | %OutputCheck %s
;
; CHECK: ^unknown$
; CHECK-NEXT: ^\(:reason-unknown timeout\)$
; CHECK-NEXT: ^\(:reason-unknown \(error "the last answer was not unknown"\)\)$
; CHECK-NEXT: ^unknown$
; CHECK-NEXT: ^\(:reason-unknown timeout\)$
; CHECK-NEXT: ^\(:reason-unknown \(error "the last answer was not unknown"\)\)$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (= (bvmul ((_ zero_extend 32) a) ((_ zero_extend 32) b)) #x7ffffffc80000005))
(assert (bvugt a #x00000001))
(assert (bvugt b #x00000001))
(check-sat)
(get-info :reason-unknown)
(reset-assertions)
(get-info :reason-unknown)
(declare-fun c () (_ BitVec 32))
(declare-fun d () (_ BitVec 32))
(assert (= (bvmul ((_ zero_extend 32) c) ((_ zero_extend 32) d)) #x7ffffffc80000005))
(assert (bvugt c #x00000001))
(assert (bvugt d #x00000001))
(check-sat)
(get-info :reason-unknown)
(reset)
(get-info :reason-unknown)
