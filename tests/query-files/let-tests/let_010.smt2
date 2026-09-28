; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :category "crafted")
(set-info :status unsat)

; The same name is rebound at three depths. After each inner let closes,
; references must resolve to the enclosing binding again.
(assert (not
  (let ((x (_ bv1 8)))
    (= (bvadd
         (let ((x (bvadd x (_ bv1 8))))          ; x = 2
           (bvadd (let ((x (bvadd x (_ bv1 8)))) ; x = 3
                    x)
                  x))                            ; 3 + 2 = 5
         x)                                      ; 5 + 1 = 6
       (_ bv6 8)))))
; CHECK-NEXT: ^unsat
(check-sat)
