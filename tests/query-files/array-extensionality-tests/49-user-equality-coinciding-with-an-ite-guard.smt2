; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^unsat
; w != v and v = 0 force w = 1, so (not (= w v)) is true, the
; if-then-else is c, and the assertion reduces to (not (= c c)).
;
; The equality's own operand is the if-then-else, so replacing it makes
; the user's assertion (= c d) -- while the guard defining d is
; c -> d = c, the very same operand pair. makeEquality therefore hands
; the guard's record straight back instead of creating one, and a
; count of records CREATED on the user's behalf stays at zero. The
; procedure then looks unused, restoreArrayITEs puts the if-then-else
; back, no guards are conjoined, and the user's proxy is left an
; unconstrained Boolean: sat, on an unsatisfiable query.
;
; Found by differential fuzzing against a brute-force oracle, not by
; reading. Fixed by recording which record ids the user asked for
; rather than how many were created, so a request that lands on an
; existing record still counts.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun c () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun v () (_ BitVec 1))
(declare-fun w () (_ BitVec 1))
(assert (not (= v w)))
(assert (= v #b0))
(assert (not (= c (ite (not (= w v)) c a))))
(check-sat)
