; RUN: %solver %s | %OutputCheck %s
;
; The other four-argument to_fp: reformatting a float, where the source is an
; *operation* rather than a leaf.
;
; Only an operation exercises the distinction. A float symbol or constant
; keeps the format it was declared or made with, so it still says "float"
; after lowering; an operation lowers to a bitvector circuit that says
; nothing. Recording "this source is an integer" in the kind therefore has to
; leave this form alone, and nothing else in the test suite reaches it -- no
; query file used a rounding-mode-taking to_fp at all.
;
; 0.75 + 0.75 = 1.5 in binary16, and widening binary16 to binary32 is exact,
; so the result is 1.5f = #x3FC00000. Read the source as a signed integer
; instead and the answer is nothing like it.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 5 11))
(assert (fp.eq x (fp #b0 #b01110 #b1000000000)))
(assert (not (fp.eq ((_ to_fp 8 24) RNE (fp.add RNE x x))
                    (fp #b0 #b01111111 #b10000000000000000000000))))
; CHECK: ^unsat
(check-sat)
