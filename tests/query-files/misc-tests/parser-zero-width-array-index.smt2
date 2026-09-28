; An array declared with a zero-width index. The productions that reject a
; non-positive width are the ones whose message was worst formed: it read
;
;   (error "syntax error: line 2 Fatal Error: parsing: BITVECTORS must be
;     of positive length:
;     token: )")
;
; -- the label of a different channel quoted inside the response, and a
; newline in the middle of it, so what should be one line a caller can read
; back arrived as two.
;
; The wording lives in one place now and says only what went wrong; the
; framing belongs to whichever channel prints it.

; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK-NOT: terminate called
; CHECK: ^\(error "syntax error: line [0-9]+ bit-vectors must be of positive length  token: \)"\)$
; CHECK: ^Fatal Error: syntax error: line [0-9]+ bit-vectors must be of positive length  token: \)$

; The response is one line: the text and the closing quote are on it, and
; nothing follows on a line of its own.
; RUN: not %solver %s 2>/dev/null | %OutputCheck %s --check-prefix=STDOUT
; STDOUT-NOT: Fatal Error
; STDOUT-NOT: ^ *token:
; STDOUT: ^\(error ".*positive length  token: \)"\)$

(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 0) (_ BitVec 8)))
(assert (= (select a #b0) #x00))
(check-sat)
