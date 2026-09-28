; A define-fun result sort, with no formals. This one never reached
; SourceSort::bitVector, so there was no assertion to hit: STP printed
; (error "... Different bit-widths specified: 1 0 ...") from the width
; comparison and then went on to answer the query anyway. A sort that does not
; exist is a parse error, not a diagnostic to keep solving through.

; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "syntax error: line [0-9]+ bit-vectors must be of positive length  token: \)"\)$
; CHECK: ^Fatal Error: syntax error: line [0-9]+ bit-vectors must be of positive length  token: \)$
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
; STDOUT: ^\(error ".*positive length  token: \)"\)$
; STDOUT-NOT: .

(set-logic QF_BV)
(define-fun f () (_ BitVec 0) (_ bv0 1))
(check-sat)
