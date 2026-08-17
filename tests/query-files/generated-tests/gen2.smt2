; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Randomly generated system of bitvector equations, converted from the
; CVC file of the same name.  Each assertion sums constant multiples of the
; declared variables and equates the sum to a constant.
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)
(declare-fun |x7| () (_ BitVec 16))
(declare-fun |x1| () (_ BitVec 16))
(declare-fun |x3| () (_ BitVec 16))
(declare-fun |x5| () (_ BitVec 16))
(declare-fun |x0| () (_ BitVec 16))
(declare-fun |x6| () (_ BitVec 16))
(declare-fun |x8| () (_ BitVec 16))
(declare-fun |x4| () (_ BitVec 16))
(declare-fun |x2| () (_ BitVec 16))
(declare-fun |x9| () (_ BitVec 16))
(assert (let ((|?let_k_0| (bvmul  #x0064 |x2|) )) 
(let ((|?let_k_1| (bvmul  #x00C5 |x4|)))
(and (= (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd (bvmul  #x007E |x0|) (bvadd (bvmul  #x006E |x5|) (bvmul  #x0039 |x9|)))))))))))  #x0067) (and (= (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd (bvmul  #x0096 |x0|) (bvadd |?let_k_0| (bvadd (bvmul  #x0084 |x3|) (bvadd (bvmul  #x004B |x4|) (bvadd (bvmul  #x00A5 |x5|) (bvadd (bvmul  #x00DA |x6|) (bvadd (bvmul  #x00B6 |x7|) (bvmul  #x00B7 |x8|)))))))))))  #x0028) (and (= (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd (bvmul  #x0099 |x0|) (bvadd (bvmul  #x00C7 |x1|) (bvadd (bvmul  #x005C |x2|) (bvadd (bvmul  #x002C |x3|) (bvadd (bvmul  #x0014 |x4|) (bvmul  #x009E |x6|)))))))))))  #x00DD) (and (= (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd (bvmul  #x00B1 |x0|) (bvadd (bvmul  #x003F |x3|) (bvadd (bvmul  #x0037 |x6|) (bvadd (bvmul  #x0016 |x7|) (bvadd (bvmul  #x004D |x8|) (bvmul  #x0096 |x9|)))))))))))  #x00D0) (and (= (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd (bvmul  #x0098 |x1|) (bvadd (bvmul  #x0090 |x3|) (bvadd (bvmul  #x00CB |x5|) (bvmul  #x00C0 |x7|)))))))))))  #x00AA) (and (= (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd |?let_k_0| (bvadd (bvmul  #x0076 |x0|) (bvadd (bvmul  #x0095 |x3|) (bvadd (bvmul  #x0003 |x4|) (bvmul  #x0077 |x7|)))))))))))  #x0082) (and (= (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd (bvmul  #x00A6 |x1|) (bvadd (bvmul  #x00B5 |x2|) (bvadd |?let_k_1| (bvmul  #x0099 |x6|)))))))))))  #x0065) (and (= (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd (bvmul  #x0043 |x1|) (bvadd (bvmul  #x0066 |x3|) (bvadd (bvmul  #x00BD |x5|) (bvadd (bvmul  #x00A3 |x8|) (bvmul  #x00C0 |x9|)))))))))))  #x0093) (and (= (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd (bvmul  #x0020 |x0|) (bvadd (bvmul  #x006D |x2|) (bvadd (bvmul  #x00A9 |x6|) (bvadd (bvmul  #x00B9 |x8|) (bvmul  #x004C |x9|)))))))))))  #x008E) (= (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd  #x0000 (bvadd |?let_k_1| (bvadd (bvmul  #x0029 |x2|) (bvmul  #x0011 |x9|)))))))))))  #x0094))))))))))) )  
)
(check-sat)
(exit)
