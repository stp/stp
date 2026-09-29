; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; A refused SMT-LIB 1 input ends the run as a fatal error did: the parser's
; line, then "Fatal Error:" and "STP Error:" with it, and exit status 255.
(benchmark b :logic QF_BV :extrafuns ((x BitVec[8])) :formula (= x y))
; CHECK: ^syntax error: line 5: syntax error  token: y
; CHECK-NEXT: ^Fatal Error: syntax error: line 5: syntax error  token: y
; CHECK-NEXT: ^STP Error: syntax error: line 5: syntax error  token: y
