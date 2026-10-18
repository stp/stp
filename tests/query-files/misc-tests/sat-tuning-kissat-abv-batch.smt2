; AUTHORS: Andrew Teylu
;
; Permission is hereby granted, free of charge, to any person obtaining a copy
; of this software and associated documentation files (the "Software"), to deal
; in the Software without restriction, including without limitation the rights
; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
; copies of the Software, and to permit persons to whom the Software is
; furnished to do so, subject to the following conditions:
;
; The above copyright notice and this permission notice shall be included in
; all copies or substantial portions of the Software.
;
; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
; THE SOFTWARE.
;
; REQUIRES: kissat
; CI also runs this with an explicit --cadical-factor=off.
; RUN: %solver --kissat --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=AUTO %s
; RUN: %solver --kissat --kissat-stable=2 --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=GLOBAL %s
; RUN: %solver --kissat --kissat-batch-only=false --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=EXPLICIT %s
; RUN: %solver --kissat --sat-tuning=off --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=OFF %s
; AUTO: ^SAT tuning: backend=kissat logic=QF_ABV session=batch profile=kissat-qf-abv-batch$
; AUTO: ^SAT tuning: cadical-factor=off \((automatic|explicit)\)$
; AUTO: ^SAT tuning: kissat-batch-only=true \(automatic\)$
; AUTO: ^SAT tuning: kissat-one-shot-stable=0 \(automatic\)$
; AUTO: ^SAT tuning: cnf-auto-threshold=0 \(automatic\)$
; AUTO: ^sat$
; GLOBAL: ^SAT tuning: backend=kissat logic=QF_ABV session=batch profile=kissat-qf-abv-batch$
; GLOBAL: ^SAT tuning: kissat-one-shot-stable=-1 \(user configuration\)$
; GLOBAL: ^sat$
; EXPLICIT: ^SAT tuning: kissat-batch-only=false \(explicit\)$
; EXPLICIT: ^sat$
; OFF: ^SAT tuning: backend=kissat logic=QF_ABV session=batch profile=off$
; OFF: ^sat$

(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const y (_ BitVec 8))
(assert (= (bvmul (select a #x00) y) #x8f))
(assert (bvugt (select a #x00) #x01))
(assert (bvugt y #x01))
(check-sat)
