; The second run of the pipeline is a second solve, and gets what a solve gets.
;
; --uf-inject-args installs injectivity the query never asserted, so an unsat
; reached over it may be the assumption's rather than the query's. The search
; settles that for itself whenever it was asked -- the implications sit behind
; a guard it can be asked about and withdraw. What it cannot settle is a
; refutation preprocessing reached before the search ever ran, and for that
; STP::TopLevelSTP decides the query a second time with the flag off.
;
; Every other route into the pipeline clears the solver's tables on the way in:
; the SMT-LIB2 frontend in Cpp_interface::resetSolver, the C API in vc_query,
; the single-query tool by never having run anything before. That second run is
; reached from inside the driver, so nothing cleared them for it, and it
; inherited the first run's substitution map. RemoveUnconstrained's array rules
; then reached a symbol the first run had already substituted and called
; UpdateSubstitutionMapFewChecks, whose whole contract is that its caller has
; established the symbol is not in the map:
;
;   Assertion `!InsideSubstitutionMap(e0) && "e0 MUST NOT be in the SolverMap"'
;
; The incremental driver never had this: IncrementalSolver::checkSat re-enters
; through checkSatBody, which clears the stale extensionality and UF state
; itself. It is here to hold both drivers to the same thing.
;
; RUN: %solver --uninterpreted-functions --array-equality --incremental=off --uf-inject-args=1 %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
; RUN: %solver --uninterpreted-functions --array-equality --incremental=on  --uf-inject-args=1 %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
; RUN: %solver --uninterpreted-functions --array-equality --incremental=off %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
; RUN: %solver --uninterpreted-functions --array-equality --incremental=on  %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
;
; As in inject-args-preserves-the-verdict.smt2, the expectations are the
; flag-off verdicts and the flag-off runs are checked against the same ones.
; A second run that never happens would pass every line above, so the trace is
; pinned too -- the batch driver says "the query", the incremental one says
; "the stack", and the pattern stops before the two part company.
;
; RUN: %solver --uninterpreted-functions --array-equality --incremental=off --uf-inject-args=1 -s %s 2>&1 | %OutputCheck --check-prefix=TRACE %s
; RUN: %solver --uninterpreted-functions --array-equality --incremental=on  --uf-inject-args=1 -s %s 2>&1 | %OutputCheck --check-prefix=TRACE %s
;
; The instance a cross-checked fuzzing campaign minimised to, reduced to four
; declarations at width 1. Both asserts are load-bearing and so is each store:
; the array assert is what preprocessing refutes, and the UF assert is the only
; reason there is an assumption standing when it does. Neither refers to the
; other, which is the point -- the refutation has nothing to do with what was
; assumed, and the second run exists to establish exactly that.
;
; The array assert writes #b0 over a cell already holding #b0, so it says an
; array differs from itself and the query is unsatisfiable. It writes at a
; symbolic index, and has to: the factory folds a self-store equality at a
; concrete index to its read equality, which settles this query before
; preprocessing is reached at all and leaves the second run nothing to be
; about -- the verdict stays unsat, but by a route that never installs the
; assumption. A symbolic index is past that rule, which keeps the refutation
; in preprocessing where this test needs it. f reads a *second*
; free array: RemoveUnconstrained's READ rule replaces a free array with a
; write to a fresh one, and it is that replacement, on the second run, that
; met the first run's substitution.
;
; CHECK: ^unsat
; CHECK: SECOND-RUN-DONE
;
; TRACE: eager 1 of those assume injectivity
; TRACE: refuted before the search could be asked about the injectivity
; TRACE: ^unsat
; TRACE: SECOND-RUN-DONE
;
(set-option :produce-models true)
(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const b (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const i (_ BitVec 1))
(declare-fun f ((_ BitVec 1)) (_ BitVec 1))
(push 1)
(assert (let ((w (store (store a #b0 #b0) #b1 #b0)))
          (distinct w (store w i #b0))))
(assert (= (f #b0) (f (select b #b0))))
(check-sat)
(echo "SECOND-RUN-DONE")
;
; The clearing the second run needs happens in the middle of a solve the
; frontend has already begun, which is the one thing about this fix that could
; cost something elsewhere: it discards the counterexample tables, the
; floating-point encoding context and the lowered UF view while the caller is
; still inside TopLevelSTP. So the session has to be shown still working
; afterwards, and working all the way to a published model -- the same three
; authorities combined-model.smt2 covers, over the same declarations the run
; above left behind.
;
; CHECK: ^sat
; CHECK: \( \(\|f\|  #b0\)  #b1 \)
; CHECK: \( \(select \|b\|  #b0\)  #b0 \)
; CHECK: SESSION-ALIVE-DONE
;
; TRACE: ^sat
; TRACE: SESSION-ALIVE-DONE
(pop 1)
(assert (= (f #b0) #b1))
(assert (= (select b #b0) #b0))
(check-sat)
(get-value ((f #b0) (select b #b0)))
(echo "SESSION-ALIVE-DONE")
