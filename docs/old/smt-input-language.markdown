This page contains a short description for the SMTLibv2 input language that STP can parse. For a longer description please read [this PDF](http://www.grammatech.com/resource/smt/SMTLIBTutorial.pdf).

Header
===========

The SMT-LIB2 format uses a header to tell the solver which type of problem is coming,  the header needed is:

```
(set-logic QF_ABV)
(set-info :smt-lib-version 2.0)
```

QF_BV is for bit-vector problems, QF_ABV is for bit-vector and array problems.

Declarations
===========

Bit-vector expressions (or terms) are constructed out of bit-vector constants, bit-vector variables and the functions listed below. In STP all variables have to declared before the point of use. An example declaration of a bit-vector variable of length, say 32, is as follows:
```
(declare-fun x () (_ BitVec 32))
```
An example of an array declaration with 32 bit indices, and 7 bit results is:
```
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 7)))
```

Functions and Terms
===========

Bit-vector variables (or terms) of length 0 are not allowed. Bit-vector constants can be represented in binary or hexadecimal format. The rightmost bit is called the least significant bit (LSB), and the leftmost bit is the most significant bit(MSB). The index of the LSB is 0, and the index of the MSB is n-1 for an n-bit constant. This convention naturally extends to all bit-vector expressions. Following are some examples of bit-vector constants:
```
#b0000111101010000, and the corresponding hex representation is #x0f50.
```

The Bit-vector implementation in STP supports a very large number of functions and predicates. The functions are categorized into word-level functions, bitwise functions, and arithmetic functions. Let t1,t2,...,tm denote some arbitrary bitvector terms.

### Word level functions

| Name          | Symbol        | Example                        |
| ---           | ---           | ---                            |
| Concatenation | `concat`      | `(concat (_ bv0 16) x)`        |
| Extraction    | `extract`     | `((_ extract 7 0) o277135888)` |
| Left Shift    | `bvlshl`      | `(bvlshl x y)`                 |
| Light Shift   | `bvlshr`      | `(bvlshr x y)`                 |
| Sign Extension| `sign_extend` | `((_ sign_extend 24) x)`       |
| Array READ    | `select`      | `(select e829 v817)`           |
| Array WRITE   | `store`       | `(store a x y)`                |

Notes:
* For extraction terms, say ((_extract i j) t), n > i >= j >= 0, where n is the length of t.
* For left shift terms, t << k is equal to k 0's appended to t. The length of t << k is n.
* For right shift terms, say t >> k, the term is equal to the bitvector obtained by k 0's followed by t[n-1:k]. The length of t >> k is n.


### Bitwise functions

| Name        | Symbol  | Example                |
| ---         | ---     | ---                    |
| Bitwise AND | `bvand` | `(bvand o1 o6)`        |
| Bitwise OR  | `bvor`  | `(bvor var29 var30)`   |
| Bitwise NOT | `bvnot` | `(bvnot (_ bv0 2000))` |
| Bitwise XOR | `bvxor` | `(bvxor e7015 e7019)`  |

The arguments of bitwise functions have the same length.

Footer
===========

After defining the problem, tell STP what to do. Usually this is to check the satisfiability, then to exit:
```
(check-sat)
(exit)
```

Examples
===========

There are many SMT-LIB2 format examples in STP's source code repository. Look for files with a .smt2 extension  here. Signed division of -1/-2 =  0, should be satisfiable:
```
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :status sat)
(assert (= (bvsdiv (_ bv3 2) (_ bv2 2)) (_ bv0 2)))
(check-sat)
(exit)
```

