; Equal carrier widths never make declared sorts interchangeable at select,
; store, or whole-array equality boundaries.
;
; RUN: not %solver %S/Inputs/wrong-index.smt2 2>&1 | %OutputCheck --check-prefix=INDEX %s
; RUN: not %solver %S/Inputs/wrong-element.smt2 2>&1 | %OutputCheck --check-prefix=ELEMENT %s
; RUN: not %solver %S/Inputs/wrong-array-sort.smt2 2>&1 | %OutputCheck --check-prefix=ARRAY %s
; INDEX: array index is not of the declared sort
; ELEMENT: stored value is not of the declared sort
; ARRAY: = requires operands of the same sort
