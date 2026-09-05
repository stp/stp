; A define-fun result sort, with formals -- a separate grammar production from
; the one in parser-zero-width-define-fun-result.smt2, and it had the same hole:
; a "Different bit-widths specified" syntax error, and then an answer.

; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "syntax error: line [0-9]+ bit-vectors must be of positive length  token: x"\)$
; CHECK: ^Fatal Error: syntax error: line [0-9]+ bit-vectors must be of positive length  token: x$
;
; The negatives have to hold over the whole output, so they get a prefix to
; themselves: OutputCheck scopes a negative directive to the region between the
; directives around it, and one placed above the first positive covers only what
; precedes the match. Alone in a prefix, this one is scoped to everything -- no
; answer, and none of the diagnostics this replaces.
; RUN: not %solver %s 2>&1 | %OutputCheck %s --check-prefix=NEG
; NEG-NOT: ^(sat|unsat)$|terminate called|Different bit-widths specified
;
; The response is one line, on stdout, and nothing follows it there: the
; "Fatal Error:"/"STP Error:" framing belongs to the other channel.
; RUN: not %solver %s 2>/dev/null | %OutputCheck %s --check-prefix=STDOUT
; STDOUT: ^\(error ".*positive length  token: x"\)$
; STDOUT-NOT: .

(set-logic QF_BV)
(define-fun f ((x (_ BitVec 8))) (_ BitVec 0) x)
(check-sat)
