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
; Adjacent unsigned bounds retain their wrap guards through push/pop.
; RUN: %solver --bv-adjacent-bounds=true --check-sanity %s | %OutputCheck %s
; RUN: %solver --bv-adjacent-bounds=true --check-sanity --incremental %s | %OutputCheck %s
; RUN: %solver --bv-adjacent-bounds=false --check-sanity %s | %OutputCheck %s
; CHECK: ^unsat$
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
(push 1)
(assert (xor (bvugt (bvadd x #x1) y)
             (and (not (= x #xf)) (bvuge x y))))
(check-sat)
(pop 1)
(push 1)
(assert (xor (bvugt y (bvadd #xf x))
             (and (not (= x #x0)) (bvuge y x))))
(check-sat)
(pop 1)
(push 1)
(assert (= x #xf))
(assert (= y #x0))
(assert (not (bvugt (bvadd x #x1) y)))
(check-sat)
(pop 1)
(push 1)
(assert (= x #x0))
(assert (= y #xf))
(assert (not (bvugt y (bvsub x #x1))))
(check-sat)
(pop 1)
(push 1)
(assert (= x #xe))
(assert (= y #xe))
(assert (bvugt (bvadd #x1 x) y))
(check-sat)
(pop 1)
(push 1)
(assert (= x #x1))
(assert (= y #x1))
(assert (bvugt y (bvadd x #xf)))
(check-sat)
(pop 1)
(push 1)
(assert (= x #x7))
(assert (= y #x0))
(assert (bvugt (bvadd x #x1) y))
(assert (not (bvsgt (bvadd x #x1) y)))
(check-sat)
(pop 1)
(declare-const p (_ BitVec 1))
(declare-const q (_ BitVec 1))
(assert (or (xor (bvugt (bvadd p #b1) q)
                 (and (not (= p #b1)) (bvuge p q)))
            (xor (bvugt q (bvsub p #b1))
                 (and (not (= p #b0)) (bvuge q p)))))
(check-sat)
