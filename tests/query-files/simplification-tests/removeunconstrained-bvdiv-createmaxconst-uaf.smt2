; RUN: %solver %s | %OutputCheck %s
; CHECK: ^sat
; Regression for a heap-use-after-free in RemoveUnconstrained's ground-path
; collapse: invertStepSymbolic's BVDIV case took a CBV from a CreateMaxConst
; temporary and read it in NonMemberBVConstEvaluator after the temporary was
; destroyed (RemoveUnconstrained.cpp, BVDIV case).
;
; NOTE: a plain build answers 'sat' whether or not the bug is present (the read
; hits freed-but-unclobbered memory); build with -fsanitize=address to observe
; the fault deterministically. Found by fuzzing STP with murxla.
(set-logic QF_BV)
(declare-const x3 (_ BitVec 104))
(declare-const x4 (_ BitVec 104))
(assert (distinct x3 (bvsrem #b00001001010001011001000101010000011100010001011000011011111110001101010110001100110111010011001010011100 ((_ rotate_left 21) #b01100011000111010101011011000101110101010101000000101000000101101100110001011000100000001001011010100001)) ((_ rotate_right 76) #b01111101111110000111111001101101100010010010011001001000010011001101001000111111100100110110111101010100) (bvudiv x4 #b01100110111101100111001101101011001101000010110011100101011111100111010101011010101110100111100111100011)))
(check-sat)
