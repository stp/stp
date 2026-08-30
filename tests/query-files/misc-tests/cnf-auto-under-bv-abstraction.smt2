; Under the BV term abstraction, `auto` resolves to the Gia backend at its
; lowest rung before the size-based choice is made, and says so; an explicit
; level is left alone, and so is a query the abstraction is not on for.
;
; RUN: %solver -s --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=ABS %s
; RUN: %solver -s --bv-term-abstraction=1 --cnf-generation-effort auto %s 2>&1 | %OutputCheck --check-prefix=ABS %s
; RUN: %solver -s --bv-term-abstraction=1 --cnf-generation-effort very-low %s 2>&1 | %OutputCheck --check-prefix=EXPLICIT %s
; RUN: %solver -s %s 2>&1 | %OutputCheck --check-prefix=OFF %s
;
; ABS: ^cnf-auto: BV term abstraction on, chose gia-low$
; ABS: ^gia: [0-9]+ AND nodes, [0-9]+ inputs, LUT3$
; ABS: ^sat$
; EXPLICIT-NOT: cnf-auto:
; EXPLICIT-NOT: ^gia:
; EXPLICIT: ^sat$
; OFF-NOT: chose gia-low
; OFF: ^cnf-auto: [0-9]+ AIG nodes, chose medium$
; OFF: ^sat$
(set-logic QF_BV)
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))
(assert (= (bvmul x y) #x0000000000000006))
(assert (bvugt x #x0000000000000001))
(assert (bvugt y #x0000000000000001))
(check-sat)
