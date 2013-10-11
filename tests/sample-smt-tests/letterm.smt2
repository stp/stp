(set-logic QF_ABV)
(set-info :smt-lib-version 2.0)

(assert
 (= (_ bv0 8)
    (let ((?x (_ bv0 8)))
         ?x)))
(check-sat)
(exit)