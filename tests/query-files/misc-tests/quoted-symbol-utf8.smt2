; Quoted symbols may contain arbitrary non-pipe printable characters,
; including multi-byte UTF-8 sequences.  The lexer's %option full builds
; a 128-column transition table (ASCII only), so bytes 0x80-0xFF inside
; |...| used to fall through to the catch-all "Illegal input character"
; rule.  This test pins the fix.
;
; The UTF-8 sequences below are:
;   U+201C  LEFT DOUBLE QUOTATION MARK  (e2 80 9c)
;   U+2013  EN DASH                     (e2 80 93)

; RUN: %solver %s 2>&1 | %OutputCheck %s
; CHECK-NOT: Illegal input character
; CHECK: ^sat$

(set-logic QF_BV)
(set-info :source |smart quote: “ and en dash: –|)
(declare-fun x () (_ BitVec 8))
(assert (= x #xff))
(check-sat)
