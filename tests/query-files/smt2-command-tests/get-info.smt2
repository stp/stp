; The flags STP can answer are reported in the standard's response format; the
; rest must answer "unsupported" rather than an error. The four the standard
; marks "support: required" (SMT-LIB 2.6, 4.1.8) are all among the former --
; :version is not pinned here because its value is the build's version stamp.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
; CHECK-NEXT: ^\(:name "STP"\)
(get-info :name)
; CHECK-NEXT: ^\(:authors "the STP team"\)
(get-info :authors)
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
(get-info :some-unknown-flag)
(assert (= x #x1))
; CHECK-NEXT: ^sat
(check-sat)
