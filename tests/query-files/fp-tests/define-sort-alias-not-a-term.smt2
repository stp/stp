; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; A sort alias is a sort, not a value. Regression test: the alias name used
; to be interned as a term symbol, so (fp.isNaN F) parsed with F as a free
; Float32 variable.
; CHECK: syntax error
(define-sort F () Float32)
(assert (fp.isNaN F))
(check-sat)
