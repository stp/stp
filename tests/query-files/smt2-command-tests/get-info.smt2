; The flags STP can answer are reported in the standard's response format; the
; rest must answer "unsupported" rather than an error. The four the standard
; marks "support: required" (SMT-LIB 2.6, 4.1.8) are all among the former.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
; CHECK-NEXT: ^\(:name "STP"\)
(get-info :name)
; The stamp is the build's and the backend list depends on the configure-time
; options, so only the shape is pinned: the version string ends with the SAT
; backends compiled into the binary, the same list --version prints. Which
; backend is behind a build changes the answers, and a session driving STP
; through SMT-LIB has no --version to ask.
; CHECK-NEXT: ^\(:version ".+ \(SAT solvers .+\)"\)$
(get-info :version)
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
; Answered; its contents are get-info-all-statistics's business, so all that
; is wanted here is that the flag is one of the answered ones.
; CHECK-NEXT: ^\(:check-sat-calls 0$
; CHECK-NEXT: ^ :cpu-time
; CHECK-NEXT: ^ :peak-memory-mb
(get-info :all-statistics)
; :reason-unknown is implemented, so it is answered rather than refused --
; and asked when the last answer was not unknown it says that, which is the
; only honest thing it can say and is not the same as being unsupported.
; CHECK-NEXT: ^\(:reason-unknown \(error "the last answer was not unknown"\)\)$
(get-info :reason-unknown)
; CHECK-NEXT: ^unsupported
(get-info :some-unknown-flag)
(assert (= x #x1))
; CHECK-NEXT: ^sat
(check-sat)
