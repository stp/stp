; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^unsat
; w != v and v = 0 force w = 1, so (not (= w v)) is true, the
; if-then-else is c, and the assertion reduces to (not (= c c)).
;
; The equality's own operand is the if-then-else, so the operand pair
; the user asked for can coincide with the pair a guard needs: the
; guard defining the replacement d is c -> d = c, and an equality
; between c and the replacement is that same pair. makeEquality then
; hands the existing record back instead of creating one.
;
; That used to matter, and cost an unsoundness. While the replacement
; happened at construction, whether the procedure ran at all was
; decided by counting the records created on the user's behalf; the
; coincidence kept that count at zero, the if-then-elses were put back
; with no guards conjoined, and the user's proxy was left a free
; Boolean -- sat, on an unsatisfiable query. Found by differential
; fuzzing against a brute-force oracle, not by reading.
;
; Nothing distinguishes the two kinds of record any more: the guards
; are minted only once the procedure is known to be running, so
; deciding that cannot depend on them. Kept as coverage of the
; coinciding shape, which is delicate for its own sake.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun c () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun v () (_ BitVec 1))
(declare-fun w () (_ BitVec 1))
(assert (not (= v w)))
(assert (= v #b0))
(assert (not (= c (ite (not (= w v)) c a))))
(check-sat)
