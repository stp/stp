; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat


(set-logic QF_ABV)
(declare-fun v470681 () (_ BitVec 12))
(declare-fun a470682 () (Array (_ BitVec 12) (_ BitVec 12)))
(assert (let ((e470685 (bvnot v470681))) 
(let ((e470686 (store a470682 (_ bv0 12) (_ bv0 12)))) 
(let ((e470687 (store e470686 e470685 e470685))) 
(let ((e470689 (select a470682 (_ bv0 12)))) 
(let ((e470690 (select a470682 e470685))) 
(let ((e470691 (select e470687 (_ bv0 12)))) 
(let ((e470693 (select a470682 e470690))) 
(let ((e470695 (select a470682 e470691))) 
(let ((e470704 (bvshl e470689 e470691))) 
(let ((e470715 (distinct e470704 e470695))) 
(let ((e470725 (bvsle v470681 e470693))) 
(let ((e470794 (and e470725 e470715))) 
e470794)))))))))))))
(check-sat)

