; A disabled UF feature does not recognize QF_UFBV, but the logic error is a
; command-local error: the following UF-free check remains usable.
;
; RUN: %solver %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error ".*Wrong input logic.*QF_UFBV"\)
; CHECK-NEXT: ^sat
;
(set-logic QF_UFBV)
(check-sat)
