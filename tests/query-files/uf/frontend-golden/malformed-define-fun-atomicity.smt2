; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error ".*f expects 1 argument but was applied to 2"\)
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^"REACHED-END"
;
; A rejected define-fun stores neither its typed recovery carrier nor its
; temporary formal. Its command latch is consumed at the closing parenthesis,
; so the independent assertion immediately following it must still take
; effect.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(define-fun malformed ((x (_ BitVec 8))) (_ BitVec 8) (f x x))
(assert false)
(check-sat)
(echo "REACHED-END")
