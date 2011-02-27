
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)

; These can be simplified by considering the context
; of the ITES they contain. 

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (ite (or a b) (not (or a b)) c ) )

(declare-fun d () Bool)
(declare-fun e () Bool)
(assert (ite (and e d) e (and e d)  ) )

(declare-fun f () Bool)
(declare-fun g () Bool)
(declare-fun h () Bool)
(assert (ite (or f g) (and g f)  g   ) )

(declare-fun i () Bool)
(declare-fun j () Bool)
(declare-fun k () Bool)
(assert (ite i (ite j i (not i)) i ))

; This doesn't simplify nicely down yet::
;  108:(OR 
;  50:m
;   52:(AND 
;     48:l
;     50:m))
(declare-fun l () Bool)
(declare-fun m () Bool)
(assert (ite (not (and l m)) m l  ) )


(check-sat)
(exit)

