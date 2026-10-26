; A format whose eb + sb passes 2^32 - 1. The C++ API refuses it; the
; parser did not, the packed width wrapped (4294967000 + 1000 is 704), and
; the query ended in an internal error, or an assertion in assertion builds.

; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "syntax error: line [0-9]+ a floating-point format is at most 4294967295 bits wide

(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 4294967000 1000))
(assert (fp.isNaN x))
(check-sat)
