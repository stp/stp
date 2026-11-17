; REQUIRES: cryptominisat
;
; Here rather than beside the other phase tests because it names its
; backend, and the query files are swept with each backend's flag prepended.
;
; The four SAT phase controls configure CaDiCaL and Kissat; no other backend
; has them. Set for one that has none, they reached the backend's
; construction inside the check, whose refusal was an engine failure:
;
;   STP Error: internal error in 'Solver::parse': the engine failed: SAT phase
;   options require CaDiCaL or Kissat; the term manager is poisoned and
;   refuses every later call; please report it [INTERNAL]
;
; They are an option error instead, by every route, as the CaDiCaL knobs are.
; Which of the two refusals arrives depends on the build: one with CaDiCaL or
; Kissat says to name it, one with neither says to build it in.
;
; A script's set-option is refused at its check.
; RUN: not %solver --SMTLIB2 --cryptominisat %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "option 'sat-phase': --sat-phase requires (--cadical or --kissat|--cadical|--kissat|a build with CaDiCaL or Kissat) \[OPTION_(CONFLICT|UNAVAILABLE)\]"\)$
;
; Nothing else is said of it, before the refusal or after: no engine failure,
; and no answer.
; RUN: not %solver --SMTLIB2 --cryptominisat %s 2>&1 | %OutputCheck --check-prefix=QUIET %s
; QUIET-NOT: INTERNAL
; QUIET-NOT: please report it
; QUIET-NOT: ^(sat|unsat|unknown)$
;
; The command line refuses the flag before it reads the input. Each of the
; four is named for itself.
; RUN: not %solver --SMTLIB2 --cryptominisat --sat-target=0 %s 2>&1 | %OutputCheck --check-prefix=CLI %s
; CLI: ^ERROR: --sat-target requires (--cadical or --kissat|--cadical|--kissat|a build with CaDiCaL or Kissat)$
; RUN: not %solver --SMTLIB2 --cryptominisat --sat-target=0 %s 2>&1 | %OutputCheck --check-prefix=CLI-QUIET %s
; CLI-QUIET-NOT: INTERNAL
; CLI-QUIET-NOT: ^(sat|unsat|unknown)$
(set-logic QF_BV)
(set-option :sat-phase 0)
(declare-fun x () (_ BitVec 8))
(assert (= x #x01))
(check-sat)
(exit)
