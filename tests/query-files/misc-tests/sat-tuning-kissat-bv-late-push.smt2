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
; RUN: %solver --kissat --incremental-auto-engage-at=1 --check-sanity -s %s 2>&1 | %OutputCheck %s
; CHECK: ^SAT tuning: backend=kissat logic=QF_BV session=batch profile=kissat-qf-bv-batch$
; CHECK: ^SAT tuning: kissat-batch-only=true \(automatic\)$
; CHECK: ^SAT tuning: bv-conditional-equality=true \(automatic\)$
; CHECK: ^SAT tuning: bv-double-equality=true \(automatic\)$
; CHECK: ^sat$
; CHECK: ^SAT tuning: backend=kissat logic=QF_BV session=incremental profile=kissat-qf-bv-incremental$
; CHECK: ^sat$
; CHECK: ^sat$

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
