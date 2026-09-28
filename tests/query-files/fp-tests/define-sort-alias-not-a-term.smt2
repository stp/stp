; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; A sort alias is a sort, not a value. Regression test: the alias name used
; to be interned as a term symbol, so (fp.isNaN F) parsed with F as a free
; Float32 variable and this file was satisfiable. The parser error-recovers
; from the bad assert (SMT-LIB error responses) and exits zero, so the check
; is the error response itself, not the exit code.
(set-logic QF_FP)
(define-sort F () Float32)
; CHECK: syntax error
(assert (fp.isNaN F))
(check-sat)
