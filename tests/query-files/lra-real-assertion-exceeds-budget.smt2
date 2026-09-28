; RUN: not %solver --SMTLIB2 %s 2>&1 | %OutputCheck %s
;
; Registering an assertion preregisters its Real atoms, and that walk does
; exact arithmetic, so it can refuse the way a Real term constructor can:
; every constant here is representable, but folding them into one linear form
; needs more than the configured 64 KiBit. registerFormula translates every
; frontend failure it sees; preregister's escaped instead, and nothing above
; it catches one, so a budget refusal on an assert reached terminate and the
; process aborted with no diagnostic at all.
;
; Reduced by delta debugging from a murxla trace.
; CHECK-L: assertion could not be registered
(set-logic QF_LRA)
(assert (let ((_let0 (- 85540413.44455765206262857018)))(let ((_let1 (* 85540413.44455765206262857018 _let0)))(let ((_let2 (* _let1 (* _let1 _let1) _let1)))(let ((_let3 (+ _let2 _let0)))(let ((_let4 (* _let3 _let2 (- _let3 85540413.44455765206262857018))))(let ((_let5 (* _let4 _let4 _let4)))(let ((_let6 (- _let5 _let0)))(let ((_let7 (+ _let5 _let0)))(let ((_let8 (* (* (- (- (- _let6 _let0)) _let0) (* (* _let7 (- (* (- _let7) _let0) _let0)) _let7)) _let6 (+ _let0 _let5))))(< _let8 _let8)))))))))))
(check-sat)
(exit)
