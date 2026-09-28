; The complement of subst-frozen-after-encode.smt2. A base equation whose
; variable never reached the solver is eliminated by substitution: it
; encodes to TRUE and the variable's model value replays by evaluation.
; A later definition of an ALREADY-encoded variable is frozen and encoded
; raw -- and its right-hand side can name the eliminated variable. That
; raw mention must first restore the eliminated equation as a permanent
; unit: a driver that just bit-blasted the mention would give x fresh,
; unconstrained bits and answer sat on this unsatisfiable stack.
; RUN: %solver --incremental %s | %OutputCheck %s
; RUN: %solver --incremental --check-sanity %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun y () (_ BitVec 8))
(assert (bvult y #x10))
; CHECK-NEXT: ^sat
(check-sat)
; x is eliminated: its equation is substituted through everything encoded
; afterwards and never itself constrains SAT bits.
(declare-fun x () (_ BitVec 8))
(assert (= x #xff))
; y's bits already exist, so this equation is frozen and encoded raw,
; carrying a raw occurrence of x. y < 16, y = x and x = 255 are together
; unsatisfiable.
(assert (= y x))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
