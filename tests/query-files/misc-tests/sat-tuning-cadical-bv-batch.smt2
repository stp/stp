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
; REQUIRES: cadical
; RUN: %solver --cadical --incremental-auto-engage-at=1 --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=AUTO %s
; RUN: %solver --cadical --sat-phase=-1 --incremental-auto-engage-at=1 --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=EXPLICIT %s
; RUN: %solver --cadical --sat-tuning=off --incremental-auto-engage-at=1 --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=OFF %s
; AUTO: ^SAT tuning: backend=cadical logic=QF_BV session=batch profile=cadical-qf-bv-batch$
; AUTO: ^SAT tuning: sat-phase=0 \(automatic\)$
; AUTO: ^sat$
; AUTO: ^SAT tuning: backend=cadical logic=QF_BV session=incremental profile=cadical-qf-bv-incremental$
; AUTO: ^sat$
; AUTO: ^sat$
; EXPLICIT: ^SAT tuning: sat-phase=-1 \(explicit\)$
; EXPLICIT: ^sat$
; EXPLICIT: ^sat$
; EXPLICIT: ^sat$
; OFF: ^SAT tuning: backend=cadical logic=QF_BV session=batch profile=off$
; OFF: ^sat$
; OFF: ^sat$
; OFF: ^sat$

(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvmul x y) #x8f))
(assert (bvugt x #x01))
(assert (bvugt y #x01))
(check-sat)
(push 1)
(assert (= x #x0b))
(check-sat)
(pop 1)
(check-sat)
