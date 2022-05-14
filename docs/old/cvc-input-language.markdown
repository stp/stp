This page contains a description for the input language that STP expects by default.

Declarations
=========

Bit-vector expressions (or terms) are constructed out of bit-vector constants, bit-vector variables and the functions listed below. In STP all variables have to declared before the point of use. An example declaration of a bit-vector variable of length, say 32, is as follows:
`x : BITVECTOR(32);`. An example of an array declaration is as follows:
```
x_arr : ARRAY BITVECTOR(32) OF BITVECTOR(5000);
```

Functions and Terms
=========

Bit-vector variables (or terms) of length 0 are not allowed. Bit-vector constants can be represented in binary or hexadecimal format. The rightmost bit is called the least significant bit (LSB), and the leftmost bit is the most significant bit(MSB). The index of the LSB is 0, and the index of the MSB is n-1 for an n-bit constant. This convention naturally extends to all bit-vector expressions. Following are some examples of bit-vector constants:
```
0bin0000111101010000, and the corresponding hex representation is 0hex0f50.
```

The Bit-vector implementation in STP supports a very large number of functions and predicates. The functions are categorized into word-level functions, bitwise functions, and arithmetic functions. Let t1,t2,...,tm denote some arbitrary bitvector terms.

Word level functions
=========

| Name           | Symbol       | Example                                                      |
| ---            | ---          | ---                                                          |
| Concatenation  | `@`          | `t1@t2@...@tm`                                               |
| Extraction     | `[i:j]`      | `x[31:26]`                                                   |
| left shift     | `<<`         | `0bin0011 << 3 = 0bin0011000`                                | 
| right shift    | `>>`         | `x[24:17] >> 5`, another example: `0bin1000 >> 3 = 0bin0001` |
| sign extension | `BVSX(bv,n)` | `BVSX(0bin100, 5) = 0bin11100`                               |
| Array READ     | `[index]`    | `x_arr[t1]`                                                  |
| Array WRITE    | `WITH`       | `x_arr WITH [index] := value`                                |

Notes:
* For extraction terms, say t[i:j], n > i >= j >= 0, where n is the length of t.0
* For Left shift terms, t << k is equal to k 0's appended to t. The length of t << k is n+k.
* For Right shift terms, say t >> k, the term is equal to the bitvector obtained by k 0's followed by t[n-1:k]. The length of t >> k is n.


Bitwise functions
=========

| Name         | Symbol   | Example              |
| ---          | ---      | ---                  |
| Bitwise AND  | `&`      | `t1 & t2 & ... & tm` |
| Bitwise OR   | `|`      | `t1 | t2 | ... | tm` |
| Bitwise NOT  | `~`      | `~t1`                |
| Bitwise XOR  | `BVXOR`  | `BVXOR(t1,t2)`       |
| Bitwise NAND | `BVNAND` | `BVNAND(t1,t2)`      |
| Bitwise NOR  | `BVNOR`  | `BVNOR(t1,t2)`       |
| Bitwise XNOR | `BVXNOR` | `BVXNOR(t1,t2)`      |

NOTE: It is required that all the arguments of bitwise functions have the same length

Arithmetic functions
=========

| Name                    | Symbol     | Example                                                               |
| ---                     | ---        | ---                                                                   |
| Bitvector Add           | `BVPLUS`   | `BVPLUS(n,t1,t2,...,tm)`                                              |
| Bitvector Multiply      | `BVMULT`   | `BVMULT(n,t1,t2)`                                                     |
| Bitvector Subtract      | `BVSUB`    | `BVSUB(n,t1,t2)`                                                      |
| Bitvector Unary Minus   | `BVUMINUS` | `BVUMINUS(t1)`                                                        |
| Bitvector Divide        | `BVDIV`    | `BVDIV(n,t1,t2)`, where `t1` is the dividend and `t2` is the divisor  |
| Signed Bitvector Divide | `SBVDIV`   | `SBVDIV(n,t1,t2)`, where `t1` is the dividend and `t2` is the divisor |
| Bitvector Modulo        | `BVMOD`    | `BVMOD(n,t1,t2)`, where `t1` is the dividend and `t2` is the divisor  |
| Signed Bitvector Modulo | `SBVMOD`   | `SBVMOD(n,t1,t2)`, where `t1` is the dividend and `t2` is the divisor |

Notes:
* the number of output bits has to specified (except unary minus).
* Inputs t1,t2 ...,tm must be of the same length
* BVUMINUS(t) is a short-hand for BVPLUS(n,~t,0bin1), where n is the length of t.
* Bitvector subtraction (BVSUB(n,t1,t2)) is a short-hand for BVPLUS(n,t1,BVUMINUS(t2))


STP also supports conditional terms (IF cond THEN t1 ELSE t2 ENDIF), where cond is boolean term, t1 and t2 can be bitvector terms. This allows us to simulate multiplexors. An example is:
```
x,y : BITVECTOR(1);
QUERY(x = IF 0bin0=x THEN y ELSE BVUMINUS(y));
```

Predicates
=========

Following are the predicates supported by STP:

| Name                            | Symbol  | Example        |
| ---                             | ---     | ---            |
| Equality                        | `=`     | `t1=t2`        |
| Less Than                       | `BVLT`  | `BVLT(t1,t2)`  |
| Greater Than                    | `BVGT`  | `BVGT(t1,t2)`  |
| Less Than Or Equal To           | `BVLE`  | `BVLE(t1,t2)`  |
| Greater Than Or Equal To        | `BVGE`  | `BVGE(t1,t2)`  |
| Signed Less Than                | `SBVLT` | `SBVLT(t1,t2)` |
| Signed Greater Than             | `SBVGT` | `SBVGT(t1,t2)` |
| Signed Less Than Or Equal To    | `SBVLE` | `SBVLE(t1,t2)` |
| Signed Greater Than Or Equal To | `SBVGE` | `SBVGE(t1,t2)` |

Note:STP requires that in atomic formulas such as `x=y`, `x` and `y` are expressions of the same length. STP accepts Boolean combination of atomic formulas.

Comments
=========

Any line whose first character is `%` is a comment.

Some Examples
=========

Example 1 illustrates the use of arithmetic, word-level and bitwise NOT operations:
```
x : BITVECTOR(5);
y : BITVECTOR(4);
yy : BITVECTOR(3);
QUERY(
 BVPLUS(9, x@0bin0000, (0bin000@(~y)@0bin11))[8:4] = BVPLUS(5, x, 0bin000@~(y[3:2]))
);
```
Example 2 illustrates the use of arithmetic, word-level and multiplexor terms:
```
bv : BITVECTOR(10);
a : BOOLEAN;
QUERY(
0bin01100000[5:3]=(0bin1111001@bv[0:0])[4:2]
AND
0bin1@(IF a THEN 0bin0 ELSE 0bin1 ENDIF)=(IF a THEN 0bin110 ELSE 0bin011 ENDIF)[1:0]
);
```

Example 3 illustrates the use of bitwise operations:
```
x, y, z, t, q : BITVECTOR(1024);

ASSERT(x=~x);
ASSERT(x&y&t&z&q = x);
ASSERT(x|y = t);
ASSERT(BVXOR(x,~x)=t);
QUERY(FALSE);
```

Example 4 illustrates the use of predicates and all the arithmetic operations:
```
x, y : BITVECTOR(8);
ASSERT(x=0hex05);
ASSERT(y = 0bin00000101);
QUERY(
BVMULT(8,x,y)=BVMULT(8,y,x)
AND
NOT(BVLT(x,y))
AND
BVLE(BVSUB(8,x,y), BVPLUS(8, x, BVUMINUS(x)))
AND
x = BVSUB(8, BVUMINUS(x), BVPLUS(8, x,0hex01))
);
```

Example 5 illustrates the use of shift functions
```
x, y : BITVECTOR(8);
z, t : BITVECTOR(12);

ASSERT(x=0hexff);
ASSERT(z=0hexff0);
QUERY(z = x << 4);
```
For invalid inputs, the COUNTEREXAMPLE command can be used to generate appropriate counterexamples. The generated counter example is essentially a bitwise assignment to the variables in the input.


