; RUN: not %solver %s 2>&1 | %OutputCheck %s
; RUN: not %solver %s 2>&1 | %OutputCheck --check-prefix=NOANSWER %s
;
; A parse STP gave up on must not leave the exit status saying the run
; succeeded. The (error ...) response was always printed, but Main::parse_file
; discarded the parser's return value, so a scripted caller classifying runs by
; exit status could not tell a rejected input from a solved one: it scored
; every refused file as a success.
;
; The diagnostic is unchanged -- the status is the whole fix.
; CHECK-L: token: bogus
; NOANSWER-NOT: ^sat$
; NOANSWER-NOT: ^unsat$
(set-logic QF_BV)
(assert (bogus))
(check-sat)
