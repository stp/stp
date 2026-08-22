; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error ".*f expects 1 argument but was applied to 2"\)
; CHECK-NEXT: ^\(error ".*f expects 1 argument but was applied to 2"\)
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^"REACHED-END"
;
; A malformed command is rejected as a unit.  The valid prefix of the first
; command must not become an assertion, and the rejected check-sat-assuming
; must neither solve its valid prefix nor print a verdict.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= (f x) #x2a))
(assert (and (= (f x) #x00) (= (f x x) #x00)))
(check-sat-assuming ((= (f x) #x00) (= (f x x) #x00)))
(check-sat)
(echo "REACHED-END")
