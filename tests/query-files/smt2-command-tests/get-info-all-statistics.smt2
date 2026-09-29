; No standard statistics are defined (SMT-LIB 2.6, 4.1.8), so what can be
; pinned is the response shape and the two things in it that do not vary from
; run to run: the session's check-sat count, and that every stage reports a
; count and a time. Times and memory are measurements, and are matched as
; numbers rather than values.
;
; The second RUN is the same file under --print-quickstat, which prints the
; run times and clears them as it goes: what get-info reports is taken across
; the solve itself, so the two must not interfere.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver -t %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
; Answered before any check rather than refused for being outside sat or
; unsat mode. No stage has done work yet, so the process figures close it.
; CHECK: ^\(:check-sat-calls 0$
; CHECK-NEXT: ^ :cpu-time [0-9]+\.[0-9]+$
; CHECK-NEXT: ^ :peak-memory-mb [0-9]+\.[0-9]+\)$
(get-info :all-statistics)
(assert (= (bvmul a b) #x0f))
(assert (bvugt a #x01))
; CHECK-NEXT: ^sat$
(check-sat)
; CHECK-NEXT: ^\(:check-sat-calls 1$
; CHECK-NEXT: ^ :cpu-time [0-9]+\.[0-9]+$
; CHECK-NEXT: ^ :peak-memory-mb [0-9]+\.[0-9]+$
; The stages the check did work in follow, each as a count and a time, and
; the last of them closes the response.
; CHECK-NEXT: ^ :[a-z-]+ [0-9]+$
; CHECK-NEXT: ^ :[a-z-]+-time-ms [0-9]+$
; CHECK: ^ :[a-z-]+-time-ms [0-9]+\)$
(get-info :all-statistics)
