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
; CI also runs this with an explicit --cadical-factor=off.
; RUN: %solver --cadical --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=AUTO %s
; RUN: %solver --cadical --cadical-factor=auto --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=EXPLICIT %s
; RUN: %solver --cadical --sat-tuning=off --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=OFF %s
; AUTO: ^SAT tuning: backend=cadical logic=QF_ABVFP session=batch profile=cadical-qf-abvfp-batch$
; AUTO: ^SAT tuning: cadical-factor=off \((automatic|explicit)\)$
; AUTO: ^sat$
; EXPLICIT: ^SAT tuning: cadical-factor=auto \(explicit\)$
; EXPLICIT: ^sat$
; OFF: ^SAT tuning: backend=cadical logic=QF_ABVFP session=batch profile=off$
; OFF: ^sat$

(set-logic QF_ABVFP)
(declare-const a (Array (_ BitVec 8) (_ FloatingPoint 5 11)))
(define-fun x () (_ FloatingPoint 5 11) (select a #x00))
(declare-const y (_ FloatingPoint 5 11))
(assert (fp.gt x ((_ to_fp 5 11) #x3c00)))
(assert (fp.lt x ((_ to_fp 5 11) #x4200)))
(assert (fp.gt y ((_ to_fp 5 11) #x3c00)))
(assert (fp.lt y ((_ to_fp 5 11) #x4200)))
(assert (fp.eq (fp.add RNE x y) ((_ to_fp 5 11) #x4400)))
(check-sat)
