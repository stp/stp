; A malformed input must be diagnosed on every channel that carries the
; diagnosis, and this file is malformed: the assertion at the bottom is
; missing an operand.
;
; There are three such channels, and each one used to lose the message:
;
;   stdout   the SMT-LIB (error "...") response, which a caller's result
;            parser reads. This one had the text, but the productions that
;            report a bad width put "Fatal Error: parsing: " and a newline
;            inside it, splitting a single-line response across two lines.
;   stderr   FatalError's own line. It was handed the empty string, so it
;            printed "Fatal Error: " and nothing after it.
;   handler  the callback a library caller installs with
;            vc_registerErrorHandler, which is how an embedder learns that
;            parsing failed. It received the same empty string, so it
;            learned nothing about why. The command line installs one that
;            prints "STP Error: ", which is what makes that path checkable
;            from here rather than only from C.
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
; CHECK: ^STP Error: syntax error: line [0-9]+ too few arguments to eq\.  token: \)$

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
