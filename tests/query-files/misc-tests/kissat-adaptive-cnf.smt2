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
; An explicit threshold exercises both adaptive choices on the same query.
; A fixed CNF effort must remain authoritative when the policy is enabled.
; REQUIRES: kissat
; RUN: %solver --kissat --sat-tuning=off --kissat-adaptive-cnf=true --cnf-generation-effort=auto --cnf-auto-threshold=2147483647 --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=SMALL %s
; RUN: %solver --kissat --sat-tuning=off --kissat-adaptive-cnf=true --cnf-generation-effort=auto --cnf-auto-threshold=1 --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=LARGE %s
; RUN: %solver --kissat --sat-tuning=off --kissat-adaptive-cnf=true --cnf-generation-effort=new-medium --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=FIXED %s
; RUN: %solver --kissat --sat-tuning=off --kissat-adaptive-cnf=false --cnf-generation-effort=auto --check-sanity -s %s 2>&1 | %OutputCheck --check-prefix=FALLBACK %s
; SMALL: ^cnf-auto: estimated [0-9]+ AND nodes, chose gia-low$
; SMALL: ^sat$
; LARGE: ^cnf-auto: estimated [0-9]+ AND nodes, chose new-medium$
; LARGE: ^sat$
; FIXED-NOT: cnf-auto:
; FIXED: ^new-medium CNF$
; FIXED: ^sat$
; FALLBACK: ^cnf-auto: [0-9]+ AIG nodes, chose medium$
; FALLBACK: ^sat$

(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= (bvand a b) #x0f))
(assert (bvult a b))
(check-sat)
(exit)
