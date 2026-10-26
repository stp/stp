; Narrow operands whose concatenation is too wide. d1..d31 double a 1-bit
; x up to 2^31 bits, a = (concat d31 d30) is 3 * 2^30, and (concat a a) is
; 3 * 2^31 = 2^32 + 2^31 bits, which wrapped in 32 bits to 2^31. That
; matched z, so the ill-sorted equality was accepted and answered sat (and
; the assertion build then aborted). The step that passes 2^32 - 1 is the
; one refused; every width before it is legal.

; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "syntax error: line [0-9]+ a bit-vector is at most 4294967295 bits wide
; CHECK-NOT: ^sat

(set-logic QF_BV)
(declare-fun x () (_ BitVec 1))
(declare-fun z () (_ BitVec 2147483648))
(assert (let ((d1 (concat x x))) (let ((d2 (concat d1 d1))) (let ((d3 (concat d2 d2))) (let ((d4 (concat d3 d3))) (let ((d5 (concat d4 d4))) (let ((d6 (concat d5 d5))) (let ((d7 (concat d6 d6))) (let ((d8 (concat d7 d7))) (let ((d9 (concat d8 d8))) (let ((d10 (concat d9 d9))) (let ((d11 (concat d10 d10))) (let ((d12 (concat d11 d11))) (let ((d13 (concat d12 d12))) (let ((d14 (concat d13 d13))) (let ((d15 (concat d14 d14))) (let ((d16 (concat d15 d15))) (let ((d17 (concat d16 d16))) (let ((d18 (concat d17 d17))) (let ((d19 (concat d18 d18))) (let ((d20 (concat d19 d19))) (let ((d21 (concat d20 d20))) (let ((d22 (concat d21 d21))) (let ((d23 (concat d22 d22))) (let ((d24 (concat d23 d23))) (let ((d25 (concat d24 d24))) (let ((d26 (concat d25 d25))) (let ((d27 (concat d26 d26))) (let ((d28 (concat d27 d27))) (let ((d29 (concat d28 d28))) (let ((d30 (concat d29 d29))) (let ((d31 (concat d30 d30))) (let ((a (concat d31 d30))) (= (concat a a) z))))))))))))))))))))))))))))))))))
(check-sat)
