; A comment ends at a carriage return as well as at a line feed (SMT-LIB
; 2.6 section 3.1). The comment on the line after the first assert ends at
; a bare CR, so the second assert that follows it on the same LF-terminated
; line is read, and the query is unsat. A lexer that reads on to the LF
; takes that assert as comment and answers sat.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-const v (_ BitVec 4))
(assert (= v #x1))
; the contradiction(assert (= v #x2))
; CHECK: ^unsat$
(check-sat)
