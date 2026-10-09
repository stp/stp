; RUN: %solver %s | %OutputCheck %s
;
; The substitution stage solves each equality for a variable and records
; the result, applying the definitions recorded so far first. It applied
; them one level deep, but a recorded value can mention a variable that a
; later row defines, so a row could be solved against stale values and carry
; them into its own. The definitions stopped being an elimination, and the
; denominators the stale values brought along compounded from row to row.
;
; Reduced from #1290, a dense 64x64 system whose exact solution needs 4-bit
; coefficients and which was given up as unknown after a minute or more. In
; this band, each row reaches back two definitions, which is enough for the
; widths to grow by about the golden ratio per row: the presolve passed the
; exact arithmetic's 65,536-bit limit and answered unknown after about ten
; seconds. Resolved transitively, it is sat at once. ddSMT could not drop
; any one of the rows.
;
; CHECK: ^sat$
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(declare-fun x7 () Real)
(declare-fun x8 () Real)
(declare-fun x9 () Real)
(declare-fun x10 () Real)
(declare-fun x11 () Real)
(declare-fun x12 () Real)
(declare-fun x13 () Real)
(declare-fun x14 () Real)
(declare-fun x15 () Real)
(declare-fun x16 () Real)
(declare-fun x17 () Real)
(declare-fun x18 () Real)
(declare-fun x19 () Real)
(declare-fun x20 () Real)
(declare-fun x21 () Real)
(declare-fun x22 () Real)
(declare-fun x23 () Real)
(declare-fun x24 () Real)
(declare-fun x25 () Real)
(declare-fun x26 () Real)
(assert (= (+ x0 x1 (- x2)) 1))
(assert (= (+ x0 x1 x2 (- x3)) 1))
(assert (= (+ x0 x1 x2 x3 (- x4)) 1))
(assert (= (+ x2 x3 x4 x5) 1))
(assert (= (+ x4 x5 x6 (- x7)) 1))
(assert (= (+ x5 x6 x7) 1))
(assert (= (+ x5 x6 x7 x8 (- x9)) 1))
(assert (= (+ x7 x8 x9 (- x10)) 1))
(assert (= (+ x7 x8 x9 (- x11)) 1))
(assert (= (+ x8 x9 x10 x11 (- x12)) 1))
(assert (= (+ x9 x10 x12 (- x13)) 1))
(assert (= (+ x10 x11 x12 x13 (- x14)) 1))
(assert (= (+ x11 x12 x13 x14 (- x15)) 1))
(assert (= (+ x12 x13 x15 (- x16)) 1))
(assert (= (+ x13 x14 x15 x16 (- x17)) 1))
(assert (= (+ x14 x15 x16 (- x18)) 1))
(assert (= (+ x15 x16 x17 (- x19)) 1))
(assert (= (+ x16 x17 x18 x19 (- x20)) 1))
(assert (= (+ x17 x18 x19 (- x21)) 1))
(assert (= (+ x18 x19 x20 x21 (- x22)) 1))
(assert (= (+ x19 x20 x22 (- x23)) 1))
(assert (= (+ x20 x21 x23 (- x24)) 1))
(assert (= (+ x21 x22 x23 x24 (- x25)) 1))
(assert (= (+ x22 x23 x24 x25 (- x26)) 1))
(assert (= (+ x23 x24 x26) 1))
(assert (= (+ x24 x25) 1))
(check-sat)
