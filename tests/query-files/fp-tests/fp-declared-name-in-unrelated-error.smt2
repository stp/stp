; RUN: not %solver %s 2>&1 | %OutputCheck %s
; RUN: not %solver %s 2>&1 | %OutputCheck --check-prefix=NOHINT %s
;
; The hint keys off the offending token, so a file that declares a
; floating-point name and then makes an unrelated mistake *at* that name is
; the case where it can misfire: bvult's arity error below reports "NaN" as
; its token, and NaN was recorded as an unresolved floating-point name by the
; very scan that preceded its declare-fun. Resolving the name has to retire
; that record, or this file gets told to set an FP logic it does not want.
; CHECK-L: unexpected TERMID_TOK, expecting RPAREN_TOK
; NOHINT-NOT-L: is a floating-point name
(set-logic QF_BV)
(declare-fun NaN () (_ BitVec 8))
(assert (bvult NaN NaN NaN))
(check-sat)
