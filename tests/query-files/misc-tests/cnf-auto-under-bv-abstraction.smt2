; Under the BV term abstraction, `auto` resolves to the Gia backend at its
; lowest rung before any other resolution, and says so; an explicit level is
; left alone, and without the abstraction the estimate-based resolution
; decides instead, printing its own line.
;
; The resolution below requires the CaDiCaL backend, so the test does too:
; a build without it keeps the size-based choice and has nothing to say, and
; a build whose default backend is CryptoMiniSat must ask for CaDiCaL.
; REQUIRES: cadical
; RUN: %solver --cadical -s --bv-term-abstraction=1 --cnf-generation-effort auto %s 2>&1 | %OutputCheck --check-prefix=ABS %s
; RUN: %solver --cadical -s --bv-term-abstraction=1 --cnf-generation-effort very-low %s 2>&1 | %OutputCheck --check-prefix=EXPLICIT %s
; RUN: %solver --cadical -s --cnf-generation-effort auto %s 2>&1 | %OutputCheck --check-prefix=OFF %s
;
; ABS: ^cnf-auto: BV term abstraction on, chose gia-low$
; ABS: ^gia: [0-9]+ AND nodes, [0-9]+ inputs, LUT3$
; ABS: ^sat$
; EXPLICIT-NOT: cnf-auto:
; EXPLICIT-NOT: ^gia:
; EXPLICIT: ^sat$
; OFF-NOT: BV term abstraction on
; OFF: ^cnf-auto: estimated [0-9]+ AND nodes, chose gia-low$
; OFF: ^sat$
(set-logic QF_BV)
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))
(assert (= (bvmul x y) #x0000000000000006))
(assert (bvugt x #x0000000000000001))
(assert (bvugt y #x0000000000000001))
(check-sat)
