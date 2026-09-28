; RUN: not %solver %s 2>&1 | %OutputCheck %s
; RUN: not %solver %s 2>&1 | %OutputCheck --check-prefix=NOANSWER %s
;
; A numeral too large for an unsigned, in a position that wants a width.
; The lexer assigned strtoul's result to an unsigned, so it wrapped: this
; declared a one-bit vector -- 2^32 + 1 modulo 2^32 -- and answered a
; question the file had not asked. Such a numeral is its own token now and
; has no production here, so it is reported instead of rounded off.
;
; Recovery is non-fatal, so the process still exits zero: the checks are the
; error response and the absence of an answer, not the exit code.
; CHECK-L: token: 4294967297  hint: 4294967297 does not fit an unsigned
; NOANSWER-NOT: ^sat$
; NOANSWER-NOT: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4294967297))
(assert (= x x))
(check-sat)
