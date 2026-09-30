; Unsupported recursive functions and datatypes consume balanced arguments.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 4))
; A comment containing an unbalanced ) must not close the command.
; CHECK-NEXT: ^unsupported
(declare-datatype Commented ( ; a comment with ) in it
  (leaf)))

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
