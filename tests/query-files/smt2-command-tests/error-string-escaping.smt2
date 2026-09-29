; An unknown quoted symbol may itself contain a double quote. Its error
; must still be one valid SMT-LIB response, with that quote doubled.
; RUN: not %solver %s 2>/dev/null | %OutputCheck %s
(set-logic QF_BV)
; CHECK: ^\(error "syntax error: line [0-9]+ .*token: \|bad""name"\)$
(assert |bad"name|)
