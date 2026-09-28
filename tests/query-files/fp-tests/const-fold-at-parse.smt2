; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
;
; All-constant floating-point nodes fold at node creation under the
; simplifying factory, so BOTH literal spellings -- (fp ...) which interns
; at parse, and ((_ to_fp e s) bits) which used to stay an unfolded
; reinterpret term solver-wide -- intern to the same ASTFPConst, and the
; constant comparison and arithmetic below never survive parsing. The
; first RUN prints its verdict only if every assertion is decided before
; CNF generation, so it fails if creation-time folding regresses. The
; --disable-simplifications run keeps the hashing factory, where nothing
; folds at creation and the ordinary blasting path answers.
;
; 1.3 > 1.0 both ways of spelling 1.3; 1.5 + 2.5 = 4.0 exactly.
;
; CHECK: ^sat
(set-logic QF_FP)
(assert (fp.gt ((_ to_fp 11 53) #x3FF4CCCCCCCCCCCD)
               (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)))
(assert (fp.gt (fp #b0 #b01111111111 #b0100110011001100110011001100110011001100110011001101)
               (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)))
(assert (= (fp.add RNE ((_ to_fp 11 53) #x3FF8000000000000)
                       ((_ to_fp 11 53) #x4004000000000000))
           ((_ to_fp 11 53) #x4010000000000000)))
(check-sat)
(exit)
