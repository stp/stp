; --incremental selects between three modes, and only the mode decides which
; solver answers a check -- never what the answer is.
;
; The observable is the driver's own -s line, which nothing but a driver solve
; prints. The -NOT directives below are not vacuous: the identical stack under
; ON prints it, so a change that stopped printing it altogether would fail
; those RUN lines rather than quietly pass these.
;
; --incremental-auto-engage-at=1 is what makes 'auto' and 'off' tell
; themselves apart on a file this short. Without it the measured pure-QF_BV
; policy delays engagement to the 32nd solve, so an automatic session of three
; checks stays on the batch pipeline and looks exactly like 'off'.

; 'on': the driver from the first solve, and a bare --incremental means it.
; RUN: %solver -s --incremental=on --check-sanity %s 2>&1 | %OutputCheck %s --check-prefix=ON
; RUN: %solver -s --incremental --check-sanity %s 2>&1 | %OutputCheck %s --check-prefix=ON

; 'auto' with the threshold reached: the push turns the session incremental.
; RUN: %solver -s --incremental=auto --incremental-auto-engage-at=1 --check-sanity %s 2>&1 | %OutputCheck %s --check-prefix=ON

; 'auto' is the default, so these two runs must agree with each other -- and
; on the QF_BV policy, three solves is short of the 32 it waits for.
; RUN: %solver -s --incremental=auto --check-sanity %s 2>&1 | %OutputCheck %s --check-prefix=BATCH
; RUN: %solver -s --check-sanity %s 2>&1 | %OutputCheck %s --check-prefix=BATCH

; 'off': never the driver, though the file pushes throughout and though the
; threshold that engaged 'auto' above is asked for explicitly.
; RUN: %solver -s --incremental=off --check-sanity %s 2>&1 | %OutputCheck %s --check-prefix=BATCH
; RUN: %solver -s --incremental=off --incremental-auto-engage-at=1 --check-sanity %s 2>&1 | %OutputCheck %s --check-prefix=BATCH

; ON: ^Incremental:
; BATCH-NOT: ^Incremental:

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

(push 1)
(assert (= x #x01))
; ON: ^sat
; BATCH: ^sat
(check-sat)

; Contradicts the level below, so this level alone is unsatisfiable.
(push 1)
(assert (bvult x #x01))
; ON: ^unsat
; BATCH: ^unsat
(check-sat)

; Popping that level must not leave the unsat behind: the replacement is
; satisfiable, and its model is the same one either way.
(pop 1)
(push 1)
(assert (= (bvadd x y) #x03))
; ON: ^sat
; BATCH: ^sat
(check-sat)
; ON: \|y\| +#x02
; BATCH: \|y\| +#x02
(get-value (y))
(exit)
