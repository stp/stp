; With UF support disabled, even a known name must not make a non-nullary
; declaration reachable.  Preserve the baseline parse abandonment.
;
; RUN: %solver %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error ".*syntax error.*x"\)
; CHECK-NOT: REACHED-END
;
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-fun x ((_ BitVec 8)) (_ BitVec 8))
(check-sat)
(echo "REACHED-END")
