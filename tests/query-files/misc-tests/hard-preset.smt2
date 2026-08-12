; --hard is a preset of option values, not a mode of its own: it must solve
; the same problems, and every option it presets must still be settable on
; the command line next to it.

; RUN: %solver --help 2>&1 | %OutputCheck %s --check-prefix=HELP
; HELP: --hard

; RUN: %solver --hard %s | %OutputCheck %s --check-prefix=SOLVE

; An option the preset covers, given explicitly: the command line wins, and
; the run is otherwise unaffected.
; RUN: %solver --hard --flattening 0 %s | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --hard --common-subsum 0 %s | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --hard --pair-extract 0 %s | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --hard --search-bias=sat %s | %OutputCheck %s --check-prefix=SOLVE

; The preset is applied before the bulk setters, so these keep the last word.
; RUN: %solver --hard --disable-simplifications %s | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --hard --size-reducing-only %s | %OutputCheck %s --check-prefix=SOLVE

; SOLVE: ^sat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvadd x (_ bv1 8)) (_ bv43 8)))
(check-sat)
(exit)
