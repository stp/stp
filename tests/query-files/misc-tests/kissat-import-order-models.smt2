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
; Each initial import order must preserve a model of the original array query,
; including when the complete batch encoding uses the one-shot path.
; REQUIRES: kissat
; RUN: %solver --kissat --kissat-import-order=0 --check-sanity %s | %OutputCheck %s
; RUN: %solver --kissat --kissat-import-order=1 --check-sanity %s | %OutputCheck %s
; RUN: %solver --kissat --kissat-import-order=2 --check-sanity %s | %OutputCheck %s
; RUN: %solver --kissat --kissat-import-order=0 --kissat-batch-only=true --check-sanity %s | %OutputCheck %s
; RUN: %solver --kissat --kissat-import-order=1 --kissat-batch-only=true --check-sanity %s | %OutputCheck %s
; RUN: %solver --kissat --kissat-import-order=2 --kissat-batch-only=true --check-sanity %s | %OutputCheck %s
; CHECK: ^sat$

(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const i (_ BitVec 8))
(declare-const j (_ BitVec 8))
(assert (distinct i j))
(assert (= (bvmul (select a i) (select a j)) #x8f))
(assert (bvugt (select a i) #x01))
(assert (bvugt (select a j) #x01))
(check-sat)
(exit)
