; RUN: %solver %s 2>&1 | %OutputCheck %s
;
; The floating-point keywords are live only under an FP set-logic (the
; fpKeyword gate in smt2.lex), so a benchmark that omits set-logic entirely --
; as fuzzer-generated ones do -- has "FloatingPoint" handed to the grammar as
; an ordinary undeclared symbol. All bison can say is that it did not expect a
; STRING_TOK there, which points nowhere near the cause. The hint names the
; token and the logics that would have made it a keyword.
;
; Recovery is non-fatal here, so the process still exits zero: the check is
; the error response, not the exit code.
; CHECK-L: hint: FloatingPoint is a floating-point name; those are recognised only after a floating-point (set-logic): QF_FP, QF_BVFP, QF_ABVFP, QF_UFFP, QF_UFBVFP, QF_AUFBVFP or one of their LRA variants
(declare-const x (_ FloatingPoint 11 53))
(check-sat)
