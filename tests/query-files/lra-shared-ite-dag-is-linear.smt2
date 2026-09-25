; RUN: %solver --SMTLIB2 --max-time 20 %s | %OutputCheck %s
;
; Forty Real if-then-elses, each one built on the one below it and named by a
; `let`, so the input is a shared DAG forty deep and under two kilobytes.
;
; Two walks over that DAG had no memo and so followed paths rather than nodes.
; `Frontend::liftRealTermItes` named the value of every ite it reached, and
; reaching one by 2^depth paths named it 2^depth times and stated 2^depth pairs
; of branch equalities for it.  The nonlinear catch-all inside presolve's
; `eliminateUnconstrained` charged every Real symbol under an atom the linear
; extractor refused, pushing every child of every node it popped with nothing
; recording what it had already seen.
;
; Both are now once per node, which is what the sibling walks beside them
; already did.  Before, twenty levels did not finish in two minutes and this
; file would not have finished at all; it now takes a hundredth of a second.
; --max-time is here so that a regression is a bounded `unknown` rather than a
; hung test.
;
; CHECK: ^sat$
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun c () Bool)
(assert
(let ((t0 (ite c (+ x 1) (- x 2))))
(let ((t1 (ite c (+ t0 1) (- t0 2))))
(let ((t2 (ite c (+ t1 1) (- t1 2))))
(let ((t3 (ite c (+ t2 1) (- t2 2))))
(let ((t4 (ite c (+ t3 1) (- t3 2))))
(let ((t5 (ite c (+ t4 1) (- t4 2))))
(let ((t6 (ite c (+ t5 1) (- t5 2))))
(let ((t7 (ite c (+ t6 1) (- t6 2))))
(let ((t8 (ite c (+ t7 1) (- t7 2))))
(let ((t9 (ite c (+ t8 1) (- t8 2))))
(let ((t10 (ite c (+ t9 1) (- t9 2))))
(let ((t11 (ite c (+ t10 1) (- t10 2))))
(let ((t12 (ite c (+ t11 1) (- t11 2))))
(let ((t13 (ite c (+ t12 1) (- t12 2))))
(let ((t14 (ite c (+ t13 1) (- t13 2))))
(let ((t15 (ite c (+ t14 1) (- t14 2))))
(let ((t16 (ite c (+ t15 1) (- t15 2))))
(let ((t17 (ite c (+ t16 1) (- t16 2))))
(let ((t18 (ite c (+ t17 1) (- t17 2))))
(let ((t19 (ite c (+ t18 1) (- t18 2))))
(let ((t20 (ite c (+ t19 1) (- t19 2))))
(let ((t21 (ite c (+ t20 1) (- t20 2))))
(let ((t22 (ite c (+ t21 1) (- t21 2))))
(let ((t23 (ite c (+ t22 1) (- t22 2))))
(let ((t24 (ite c (+ t23 1) (- t23 2))))
(let ((t25 (ite c (+ t24 1) (- t24 2))))
(let ((t26 (ite c (+ t25 1) (- t25 2))))
(let ((t27 (ite c (+ t26 1) (- t26 2))))
(let ((t28 (ite c (+ t27 1) (- t27 2))))
(let ((t29 (ite c (+ t28 1) (- t28 2))))
(let ((t30 (ite c (+ t29 1) (- t29 2))))
(let ((t31 (ite c (+ t30 1) (- t30 2))))
(let ((t32 (ite c (+ t31 1) (- t31 2))))
(let ((t33 (ite c (+ t32 1) (- t32 2))))
(let ((t34 (ite c (+ t33 1) (- t33 2))))
(let ((t35 (ite c (+ t34 1) (- t34 2))))
(let ((t36 (ite c (+ t35 1) (- t35 2))))
(let ((t37 (ite c (+ t36 1) (- t36 2))))
(let ((t38 (ite c (+ t37 1) (- t37 2))))
(let ((t39 (ite c (+ t38 1) (- t38 2))))
(> t39 0))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
