; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/malformed-check-sat-assuming.smt2 2>&1 | %OutputCheck --check-prefix=ASSUMING %s
; CHECK-NEXT: ^\(error ".*f expects 1 argument but was applied to 2"\)
; CHECK-NOT: ^sat
; CHECK-NOT: ^"REACHED-END"
;
; ASSUMING: ^\(error ".*f expects 1 argument but was applied to 2"\)
; ASSUMING-NOT: ^sat
; ASSUMING-NOT: ^unsat
; ASSUMING-NOT: ^"REACHED-END"
;
; A malformed command is refused as a unit and the session ends there. The
; valid prefix of the command must not become an assertion on the way out, and
; a rejected check-sat-assuming must neither solve its valid prefix nor print
; a verdict.
;
; Both used to recover, and the recovery needed a fix of its own: a malformed
; assumption was consumed by the internal AddAssert, which dropped the
; poisoned assumption and left the latch for the NEXT assertion to consume, so
; the (assert false) in the Inputs file vanished and it answered sat. Nothing
; follows a refusal now, so that shape has nowhere left to go -- the Inputs
; file keeps the (assert false) so a regression that resumed the session would
; have to answer it.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= (f x) #x2a))
(assert (and (= (f x) #x00) (= (f x x) #x00)))
(check-sat)
(echo "REACHED-END")
