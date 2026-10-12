; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :category "crafted")
(set-info :status unsat)

; Two binding lists are pending at once when the innermost let is read: the
; rebindings of k to 2 and to 3 must both stay hidden, so o sees k = 1.
; Each list's own body still sees its own k.
(assert (not
  (let ((k (_ bv1 4)))
    (let ((k (_ bv2 4))
          (m (let ((k (_ bv3 4)) (n (let ((o k)) o)))
               (bvadd (bvmul k (_ bv4 4)) n))))     ; 3 * 4 + 1 = 13
      (= (bvadd m k) (_ bv15 4))))))                ; 13 + 2 = 15
; CHECK-NEXT: ^unsat
(check-sat)
