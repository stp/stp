; RUN: not %solver %s 2>&1 | %OutputCheck %s
; RUN: not %solver %s 2>&1 | %OutputCheck --check-prefix=NOANSWER %s
;
; Accepting the *LRA logic names does not give STP a theory of reals. A real
; that is not the literal argument of to_fp has no production, so it is
; refused rather than quietly dropped -- answering a query STP had not fully
; read is the one outcome that would be worse than refusing it.
;
; Resolving a sort is fatal where recovering from a bison error is not, so
; this one does exit non-zero.
; CHECK-L: unknown sort (not built in, and not a declared sort)  token: Real
; NOANSWER-NOT: ^sat$
; NOANSWER-NOT: ^unsat$
(set-logic QF_BVFPLRA)
(declare-fun r () Real)
(assert (> r 0.0))
(check-sat)
