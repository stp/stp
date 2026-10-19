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
; The SMT-LIB option reaches complete encodings without changing the
; ordinary mode of an incremental session.
; REQUIRES: kissat
; RUN: %solver --kissat --sat-tuning=off --kissat-batch-only=true --kissat-stable=2 --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=BATCH %s
; BATCH: ^Kissat one-shot: on$
; BATCH: ^Kissat search:.* stable=0
; BATCH: ^sat$
; RUN: %solver --kissat --sat-tuning=off --incremental --kissat-batch-only=true --kissat-stable=2 --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=INCREMENTAL %s
; INCREMENTAL: ^Kissat search:.* stable=2
; INCREMENTAL: ^sat$

(set-logic QF_BV)
(set-option :kissat-one-shot-stable 0)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvugt x #x01))
(assert (bvugt y #x01))
(assert (bvult x #x20))
(assert (bvult y #x20))
(assert (= (bvmul x y) #x8f))
(check-sat)
