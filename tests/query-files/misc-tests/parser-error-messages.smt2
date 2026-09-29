; A malformed input must be diagnosed on every channel that carries the
; diagnosis, and this file is malformed: the assertion at the bottom is
; missing an operand.
;
; The regular channel carries the SMT-LIB error response; the diagnostic
; channel carries the explanatory log line. A native API caller may also
; install a fatal-error observer. The CLI lets parsing unwind so engine
; type errors reach the regular channel before the process exits.
;
; Pinning text after each label is the whole point: a blank message is what
; the bug looked like, and only a positive match rules it out. The line
; number is deliberately left as a pattern, so that editing this comment
; does not rewrite the test.
;
; The 'not' wrapper checks the exit status through the pipe, as in
; bad-cli-options.smt2 next door -- a parser that crashed rather than
; exiting would fail the RUN line on its own.

; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK-NOT: terminate called
; CHECK: ^\(error "syntax error: line [0-9]+ too few arguments to eq\.  token: \)"\)$
; CHECK: ^Fatal Error: syntax error: line [0-9]+ too few arguments to eq\.  token: \)$

; The response on stdout is one line and carries no "Fatal Error" wording:
; it is a protocol answer, not a log line.
; RUN: not %solver %s 2>/dev/null | %OutputCheck %s --check-prefix=STDOUT
; STDOUT-NOT: Fatal Error
; STDOUT: ^\(error "syntax error: line [0-9]+ too few arguments to eq\.  token: \)"\)$

; And a caller reading only stderr still learns the reason.
; RUN: not %solver %s 2>&1 >/dev/null | %OutputCheck %s --check-prefix=STDERR
; STDERR: ^Fatal Error: syntax error: line [0-9]+ too few arguments to eq\.  token: \)$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= x ))
(check-sat)
