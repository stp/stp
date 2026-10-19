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
; RUN: %solver --kissat --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=AUTO %s
; RUN: %solver --kissat --sat-phase=-1 --cnf-generation-effort=new-medium --kissat-adaptive-cnf=false --kissat-import-order=0 --kissat-incremental-greedy=0 --kissat-batch-only=false --bv-conditional-equality=false --bv-double-equality=false --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=EXPLICIT %s
; RUN: %solver --kissat --search-bias=none --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=BIAS %s
; RUN: %solver --kissat --sat-tuning=off --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=OFF %s
; AUTO: ^SAT tuning: backend=kissat logic=QF_BV session=batch profile=kissat-qf-bv-batch$
; AUTO: ^SAT tuning: sat-phase=0 \(automatic\)$
; AUTO: ^SAT tuning: cnf-generation-effort=auto \(automatic\)$
; AUTO: ^SAT tuning: kissat-adaptive-cnf=true \(automatic\)$
; AUTO: ^SAT tuning: kissat-import-order=2 \(automatic\)$
; AUTO: ^SAT tuning: kissat-incremental-greedy=4 \(automatic\)$
; AUTO: ^SAT tuning: kissat-batch-only=true \(automatic\)$
; AUTO: ^SAT tuning: bv-conditional-equality=true \(automatic\)$
; AUTO: ^SAT tuning: bv-double-equality=true \(automatic\)$
; AUTO: ^sat$
; EXPLICIT: ^SAT tuning: sat-phase=-1 \(explicit\)$
; EXPLICIT: ^SAT tuning: cnf-generation-effort=new-medium \(explicit\)$
; EXPLICIT: ^SAT tuning: kissat-adaptive-cnf=false \(explicit\)$
; EXPLICIT: ^SAT tuning: kissat-import-order=0 \(explicit\)$
; EXPLICIT: ^SAT tuning: kissat-incremental-greedy=0 \(explicit\)$
; EXPLICIT: ^SAT tuning: kissat-batch-only=false \(explicit\)$
; EXPLICIT: ^SAT tuning: bv-conditional-equality=false \(explicit\)$
; EXPLICIT: ^SAT tuning: bv-double-equality=false \(explicit\)$
; EXPLICIT: ^sat$
; BIAS: ^SAT tuning: sat-phase=-1 \(user configuration\)$
; BIAS: ^SAT tuning: bv-conditional-equality=true \(automatic\)$
; BIAS: ^SAT tuning: bv-double-equality=true \(automatic\)$
; BIAS: ^sat$
; OFF: ^SAT tuning: backend=kissat logic=QF_BV session=batch profile=off$
; OFF: ^sat$

(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvmul x y) #x8f))
(assert (bvugt x #x01))
(assert (bvugt y #x01))
(check-sat)
