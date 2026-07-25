; The flags STP can answer are reported in the standard's response format; the
; rest must answer "unsupported" rather than an error.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
; CHECK-NEXT: ^\(:name "STP"\)
(get-info :name)
; CHECK-NEXT: ^\(:error-behavior immediate-exit\)
(get-info :error-behavior)
; CHECK-NEXT: ^\(:assertion-stack-levels 0\)
(get-info :assertion-stack-levels)
(push 1)
; CHECK-NEXT: ^\(:assertion-stack-levels 1\)
(get-info :assertion-stack-levels)
(pop 1)
; CHECK-NEXT: ^unsupported
(get-info :all-statistics)
; CHECK-NEXT: ^unsupported
(get-info :reason-unknown)
; CHECK-NEXT: ^unsupported
(get-info :authors)
; CHECK-NEXT: ^unsupported
(get-info :some-unknown-flag)
(assert (= x #x1))
; CHECK-NEXT: ^sat
(check-sat)
