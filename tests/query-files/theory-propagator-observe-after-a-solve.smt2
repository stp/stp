; REQUIRES: cadical
; RUN: %solver --SMTLIB2 --cadical --bv-eq-abstraction=1 --bv-eq-abstraction-constant-side=1 --cnf-generation-effort=gia-high --search-bias sat %s | %OutputCheck %s
;
; The LRA propagator is connected once the CNF binds its atoms, which is
; always after a first solve. CaDiCaL only lets a variable become observed
; while nothing has put it on the extension stack, so an atom its inprocessing
; eliminated or substituted during that first solve can no longer be observed:
; add_observed_var fails its own API contract and aborts the process -- exit
; 134, no answer, where the answer is sat. SATSolver::expectTheoryPropagator()
; now retires that inprocessing for the rest of the query, which keeps every
; atom observable.
;
; Reduced from a QF_FPLRA fuzzer case. The floating-point division is what
; makes the first CNF large enough for elimination to reach one of the two Real
; atoms -- a bit-vector formula of 600k variables in its place does not -- and
; "--search-bias sat" is what makes elimination try ten times as hard. All
; five options are needed, and so is the order of the declarations below,
; which decides the numbering elimination works on: this file is a witness,
; not a robust trigger. TheoryPropagatorExpectation_Test checks the backend
; directly, and does not depend on any of that.
;
; The abort itself is only visible against a CaDiCaL that still carries this
; contract check. STP's own copy is patched to taint and restore instead
; (cmake/deps-utils/cadical-observe-witness-taint-restore.patch), and that
; patch reaches only the ExternalProject rung -- never a CaDiCaL named with
; -DCADICAL_DIR=... or already installed.
;
; Not named lra-*: that glob is swept under each backend that can host the
; propagator, with the backend appended to the RUN line, and this file names
; one of its own.
(set-logic QF_FPLRA)
(declare-const x Bool)
(declare-fun f () Float64)
(declare-fun g () Float64)
(declare-fun r2 () Real)
(declare-fun r1 () Real)
(assert (and (< r1 r2) (or x (distinct r1 r2)) (or x (fp.geq (fp.div RNA g (fp.div RTP g f)) (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))))))
; CHECK: ^sat
(check-sat)
