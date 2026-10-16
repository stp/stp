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
; The adaptive policy keeps the ordinary array-refinement eligibility gate.
; Disable the optional late eager choice so this query still refines.
; REQUIRES: kissat
; RUN: %solver --kissat --sat-tuning=off --kissat-adaptive-cnf=true --cnf-generation-effort=auto --array-late-read-limit=0 --check-sanity -s %s 2>&1 | %OutputCheck %s
; CHECK-NOT: cnf-auto: estimated
; CHECK: ^cnf-auto: [0-9]+ AIG nodes, chose medium$
; CHECK-NOT: cnf-auto: estimated
; CHECK: ^sat$

(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun i0 () (_ BitVec 32))
(declare-fun i1 () (_ BitVec 32))
(declare-fun i2 () (_ BitVec 32))
(declare-fun i3 () (_ BitVec 32))
(declare-fun i4 () (_ BitVec 32))
(declare-fun i5 () (_ BitVec 32))
(declare-fun i6 () (_ BitVec 32))
(declare-fun i7 () (_ BitVec 32))
(declare-fun i8 () (_ BitVec 32))
(declare-fun i9 () (_ BitVec 32))
(declare-fun i10 () (_ BitVec 32))
(declare-fun i11 () (_ BitVec 32))
(assert (bvult (select a i0) (select a i1)))
(assert (bvult (select a i1) (select a i2)))
(assert (bvult (select a i2) (select a i3)))
(assert (bvult (select a i3) (select a i4)))
(assert (bvult (select a i4) (select a i5)))
(assert (bvult (select a i5) (select a i6)))
(assert (bvult (select a i6) (select a i7)))
(assert (bvult (select a i7) (select a i8)))
(assert (bvult (select a i8) (select a i9)))
(assert (bvult (select a i9) (select a i10)))
(assert (bvult (select a i10) (select a i11)))
(assert (bvugt (bvadd (select a i0) (select a i11)) #x00000010))
(check-sat)
