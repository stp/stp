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
; Cancel a doubled addend, retaining modular and scoped semantics.
; RUN: %solver --bv-double-equality=true --check-sanity %s | %OutputCheck %s
; RUN: %solver --bv-double-equality=true --check-sanity --incremental %s | %OutputCheck %s
; RUN: %solver --bv-double-equality=false --check-sanity %s | %OutputCheck %s
; CHECK: ^unsat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$

(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(declare-const z (_ BitVec 4))
(push 1)
(assert (= z (bvadd x y)))
(assert (= z (bvshl x #x1)))
(assert (distinct x y))
(check-sat)
(pop 1)
(push 1)
(assert (= (bvmul #x2 x) (bvadd y x)))
(assert (distinct x y))
(check-sat)
(pop 1)
(push 1)
(assert (= (bvadd x y) (concat ((_ extract 2 0) x) #b0)))
(assert (distinct x y))
(check-sat)
(pop 1)
(push 1)
(assert (= x #xf))
(assert (= y #xf))
(assert (= z #xe))
(assert (= z (bvadd x y)))
(assert (= z (bvshl x #x1)))
(check-sat)
(pop 1)
(push 1)
(assert (= x #x1))
(assert (= y #x3))
(assert (= z #x2))
(assert (= (bvadd x y) (bvshl z #x1)))
(assert (distinct x y))
(check-sat)
(pop 1)
(push 1)
(assert (= x #x8))
(assert (= y #x4))
(assert (= (bvadd x y) (bvashr x #x1)))
(assert (distinct x y))
(check-sat)
(pop 1)
(push 1)
(assert (= x #x3))
(assert (= y #x1))
(assert (= z #x2))
(assert (= (bvadd x y z) (bvshl x #x1)))
(assert (distinct x y))
(check-sat)
(pop 1)
(push 1)
(assert (= x #x1))
(assert (= y #x3))
(assert (= (bvadd x y) (bvshl x #x2)))
(assert (distinct x y))
(check-sat)
(pop 1)
(declare-const p (_ BitVec 1))
(declare-const q (_ BitVec 1))
(assert (not (= (= (bvadd p q) (bvshl p #b1)) (= p q))))
(check-sat)
