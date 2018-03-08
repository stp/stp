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

<table class="zab1">
<tr>
<th>Name</th>
<th>Symbol</th>
<th>Example</th>
</tr>

<tr>
<td>Concatenation</td>
<td>@</td>
<td>t1@t2@...@tm</td>
</tr>

<tr>
<td>Extraction</td>
<td>[i:j]</td>
<td>x[31:26]</td>
</tr>

<tr>
<td>left shift</td>
<td><<</td>
<td>0bin0011 << 3 = 0bin0011000</td>
</tr>

<tr>
<td>right shift</td>
<td>>></td>
<td>x[24:17] >> 5, another example: 0bin1000 >> 3 = 0bin0001</td>
</tr>

<tr>
<td>sign extension</td>
<td>BVSX(bv,n)</td>
<td>BVSX(0bin100, 5) = 0bin11100</td>
</tr>

<tr>
<td>Array READ</td>
<td>[index]</td>
<td>x_arr[t1]</td>
</tr>

<tr>
<td>Array WRITE</td>
<td>WITH</td>
<td>x_arr WITH [index] := value</td>
</tr>
</table class="zab1">

Notes:
* For extraction terms, say t[i:j], n > i >= j >= 0, where n is the length of t.0
* For Left shift terms, t << k is equal to k 0's appended to t. The length of t << k is n+k.
* For Right shift terms, say t >> k, the term is equal to the bitvector obtained by k 0's followed by t[n-1:k]. The length of t >> k is n.


Bitwise functions
=========

<table class="zab1">
<tr>
<th>Name</th>
<th>Symbol</th>
<th>Example</th>
</tr>

<tr>
<td>Bitwise AND</td>
<td>&</td>
<td>t1 & t2 & ... & tm</td>
</tr>

<tr>
<td>Bitwise OR</td>
<td>|</td>
<td>t1 | t2 | t3 | ... | tm</td>
</tr>

<tr>
<td>Bitwise NOT</td>
<td>~</td>
<td>~t1</td>
</tr>

<tr>
<td>Bitwise XOR</td>
<td>BVXOR</td>
<td>BVXOR(t1,t2)</td>
</tr>

<tr>
<td>Bitwise NAND</td>
<td>BVNAND</td>
<td>BVNAND(t1,t2)</td>
</tr>

<tr>
<td>Bitwise NOR</td>
<td>BVNOR</td>
<td>BVNOR(t1,t2)</td>
</tr>

<tr>
<td>Bitwise XNOR</td>
<td>BVXNOR</td>
<td>BVXNOR(t1,t2)</td>
</tr>
</table class="zab1">
NOTE: It is required that all the arguments of bitwise functions have the same length

Arithmetic functions
=========

<table class="zab1">
<tr>
<th>Name</th>
<th>Symbol</th>
<th>Example</th>
</tr>

</tr>
<td>Bitvector Add</td>
<td>BVPLUS</td>
<td>BVPLUS(n,t1,t2,...,tm)</td>
</tr>

</tr>
<td>Bitvector Mult</td>
<td>BVMULT</td>
<td>BVMULT(n,t1,t2)</td>
</tr>

</tr>
<td>Bitvector subtract</td>
<td>BVSUB</td>
<td>BVSUB(n,t1,t2)</td>
</tr>

</tr>
<td>Bitvector Unary Minus</td>
<td>BVUMINUS</td>
<td>BVUMINUS(t1)</td>
</tr>

</tr>
<td>Bitvector Div</td>
<td>BVDIV</td>
<td>BVDIV(n,t1,t2), where t1 is the dividend and t2 is the divisor</td>
</tr>

</tr>
<td>Signed Bitvector Div</td>
<td>SBVDIV</td>
<td>SBVDIV(n,t1,t2), where t1 is the dividend and t2 is the divisor</td>
</tr>

</tr>
<td>Bitvector Modulo</td>
<td>BVMOD</td>
<td>BVMOD(n,t1,t2), where t1 is the dividend and t2 is the divisor</td>
</tr>

</tr>
<td>Signed Bitvector Modulo</td>
<td>SBVMOD</td>
<td>SBVMOD(n,t1,t2), where t1 is the dividend and t2 is the divisor</td>
</tr>
</table class="zab1">

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

<table class="zab1">
<tr>
<th>Name</th>
<th>Symbol</th>
<th>Example</th>
</tr>

<tr>
<td>Equality</td>
<td>=</td>
<td>t1=t2</td>
</tr>

<tr>
<td>Less Than</td>
<td>BVLT</td>
<td>BVLT(t1,t2)</td>
</tr>

<tr>
<td>Greater Than</td>
<td>BVGT</td>
<td>BVGT(t1,t2)</td>
</tr>

<tr>
<td>Less Than Or Equal To</td>
<td>BVLE</td>
<td>BVLE(t1,t2)</td>
</tr>

<tr>
<td>Greater Than Or Equal To</td>
<td>BVGE</td>
<td>BVGE(t1,t2)</td>
</tr>

<tr>
<td>Signed Less Than</td>
<td>SBVLT</td>
<td>SBVLT(t1,t2)</td>
</tr>

<tr>
<td>Signed Greater Than</td>
<td>SBVGT</td>
<td>SBVGT(t1,t2)</td>
</tr>

<tr>
<td>Signed Less Than Or Equal To</td>
<td>SBVLE</td>
<td>SBVLE(t1,t2)</td>
</tr>

<tr>
<td>Signed Greater Than Or Equal To</td>
<td>SBVGE</td>
<td>SBVGE(t1,t2)</td>
</tr>
</table class="zab1">

Note:STP requires that in atomic formulas such as x=y, x and y are expressions of the same length. STP accepts Boolean combination of atomic formulas.

Comments
=========

Any line whose first character is % is a comment.

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


