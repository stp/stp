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
; RUN: %solver --cadical --sat-tuning=auto --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=AUTO %s
; RUN: %solver --cadical --sat-tuning=auto --sat-phase=-1 --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=EXPLICIT %s
; RUN: %solver --cadical --sat-tuning=off --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=OFF %s
; AUTO: ^SAT tuning: backend=cadical logic=QF_ABVFP session=incremental profile=cadical-qf-abvfp-forced-incremental$
; AUTO: ^SAT tuning: sat-phase=0 \(automatic\)$
; AUTO: ^sat$
; AUTO: ^unsat$
; AUTO: ^sat$
; EXPLICIT: ^SAT tuning: backend=cadical logic=QF_ABVFP session=incremental profile=cadical-qf-abvfp-forced-incremental$
; EXPLICIT: ^SAT tuning: sat-phase=-1 \(explicit\)$
; EXPLICIT: ^sat$
; EXPLICIT: ^unsat$
; EXPLICIT: ^sat$
; OFF: ^SAT tuning: backend=cadical logic=QF_ABVFP session=incremental profile=off$
; OFF: ^sat$
; OFF: ^unsat$
; OFF: ^sat$

(set-logic QF_ABVFP)
(set-option :incremental true)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const y (_ BitVec 8))
(declare-const f (_ FloatingPoint 8 24))
(assert (= (bvmul (select a #x00) y) #x8f))
(assert (bvugt (select a #x00) #x01))
(assert (bvugt y #x01))
(assert (fp.eq (fp.add RNE f ((_ to_fp 8 24) #x3f800000)) ((_ to_fp 8 24) #x40000000)))
(check-sat)
(push 1)
(assert (fp.isNaN f))
(check-sat)
(pop 1)
(check-sat)
