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

; RUN: %solver --bv-conditional-equality=true --check-sanity %s | %OutputCheck %s
; RUN: %solver --bv-conditional-equality=false --check-sanity %s | %OutputCheck %s
; RUN: %solver --bv-conditional-equality=true --incremental --check-sanity %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK: ^unsat$
; CHECK: ^sat$

(set-logic QF_BV)
(declare-const c Bool)
(declare-const x (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (ite c (= x a) (= x b)))
(assert (= a #x09))
(assert (= b #x0b))
(assert (distinct x a))
(check-sat)
(push 1)
(assert c)
(check-sat)
(pop 1)
(check-sat)
