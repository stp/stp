; AUTHORS: Andrew Teylu
; SPDX-License-Identifier: MIT
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
; RUN: %solver --kissat --incremental=on --kissat-lucky-probe=true --check-sanity -d %s | %OutputCheck %s
; RUN: %solver --kissat --incremental=on --kissat-lucky-probe=false --check-sanity -d %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const contradict Bool)
(assert (= (bvmul a b) #x21))
(assert (bvult a b))
(assert (=> contradict (= a b)))
(check-sat)
(check-sat-assuming (contradict))
(check-sat-assuming ((not contradict)))
(push 1)
(assert (= a b))
(check-sat)
(pop 1)
(check-sat)
; Fresh symbols and clauses are introduced after several SAT calls.
(declare-const fresh (_ BitVec 8))
(assert (= fresh (bvadd a b)))
(check-sat)
(assert (distinct fresh (bvadd a b)))
(check-sat)
