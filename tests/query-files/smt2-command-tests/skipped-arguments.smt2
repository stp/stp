; define-sort, define-fun-rec, define-funs-rec and declare-datatype(s) have
; arguments STP has no use for, so the lexer swallows the rest of the
; s-expression. If it miscounted, the commands after these would be eaten
; silently -- hence the check-sat at the end of every group.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 4))

; CHECK-NEXT: ^unsupported
(define-sort BV4 () (_ BitVec 4))
; CHECK-NEXT: ^unsupported
(define-sort Parametric (T) (Array T T))
; CHECK-NEXT: ^unsupported
(define-sort Deep () (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 4))))

; Arguments spread over several lines.
; CHECK-NEXT: ^unsupported
(define-sort
   Multi
   ()
   (_ BitVec 4)
)

; A comment containing an unbalanced ) inside the skipped region.
; CHECK-NEXT: ^unsupported
(define-sort Commented () ; a comment with ) in it
  (_ BitVec 4))

; A quoted symbol containing an unbalanced ) inside the skipped region.
; CHECK-NEXT: ^unsupported
(declare-datatype |weird ) name| ((leaf)))

; CHECK-NEXT: ^unsupported
(define-fun-rec f ((a (_ BitVec 4))) (_ BitVec 4) (bvadd a #x1))
; CHECK-NEXT: ^unsupported
(define-funs-rec ((g ((a (_ BitVec 4))) (_ BitVec 4)) (h ((b (_ BitVec 4))) (_ BitVec 4))) ((bvadd a #x1) (bvsub b #x1)))
; CHECK-NEXT: ^unsupported
(declare-datatype Colour ((red) (green) (blue)))
; CHECK-NEXT: ^unsupported
(declare-datatypes ((Lst 0) (Pair 0)) (((nil) (cons (hd (_ BitVec 4)) (tl Lst))) ((mk (fst (_ BitVec 4)) (snd (_ BitVec 4))))))

; Everything after all that must still work.
(assert (= x #x1))
; CHECK-NEXT: ^sat
(check-sat)
(reset-assertions)
(declare-fun x () (_ BitVec 4))
(assert (and (= x #x1) (= x #x2)))
; CHECK-NEXT: ^unsat
(check-sat)
