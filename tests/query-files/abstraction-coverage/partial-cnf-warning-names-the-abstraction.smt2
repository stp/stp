; A CNF an abstraction produced says so, and does not send the reader to a
; flag that cannot help.
;
; There are two reasons a CNF STP writes out can be incomplete and they are not
; the same reason. Array read refinement leaves out congruence axioms over a
; faithful bit-vector layer, and --ackermanize is the flag that puts them all in
; up front. A bit-vector abstraction leaves out the arithmetic itself: what
; comes out over-approximates the query, and no flag completes it -- turning the
; abstraction off gives a different encoding rather than the same one finished.
;
; One sentence covered both and named "-r", which is --ackermanize. On an
; array-free query with the abstraction on that advice is inert: adding it
; changes nothing about the CNF and cannot, because the incompleteness has
; nothing to do with reads.
;
; The second leg is the one that said nothing at all. --output-CNF writes the
; file whether or not --exit-after-CNF is given, so an over-approximate CNF
; could be written to disk with no warning anywhere.
;
; RUN: %solver --incremental=off --exit-after-CNF --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=EXITING %s
; RUN: %solver --incremental=off --output-CNF --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=WRITTEN %s
; RUN: %solver --incremental=off --exit-after-CNF %s 2>&1 | %OutputCheck --check-prefix=EXACT %s
;
; EXITING: exiting after generating the first CNF
; EXITING: over-approximation of the query
;
; WRITTEN: --output-CNF is an over-approximation of the query
;
; That leg writes output_0.cnf into this test's directory in the build tree.
; The name is per-process and this is the only test in the suite that asks for
; one, so it is overwritten rather than accumulated.
;
; With no abstraction and no arrays the CNF is the whole query, so there is
; nothing to warn about and nothing is said.
; EXACT-NOT: over-approximation of the query
; EXACT-NOT: array read refinement
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(assert (bvult (bvmul a b) (_ bv100 64)))
(assert (bvugt a (_ bv7 64)))
(assert (bvugt b (_ bv7 64)))
(assert (distinct a b))
(check-sat)
(exit)
