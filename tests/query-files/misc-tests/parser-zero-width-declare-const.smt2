; (_ BitVec 0) is not a sort, and saying so is the parser's job.
;
; SourceSort::bitVector asserts a positive width, so a zero reached it and
; aborted inside a header on an asserting build. Without assertions the symbol
; kept a zero value width, which the legacy width checks read as a Boolean, and
; the query went on to be answered and to print a model at the wrong sort.
;
; This is declare-const; the sibling files cover the other sort productions.
; Each is its own file because the refusal is fatal, so one file exercises one
; rule and nothing after it.

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
(declare-const a (_ BitVec 0))
(assert (distinct a a))
(check-sat)
