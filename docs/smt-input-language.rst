This page contains a short description for the SMTLibv2 input language
that STP can parse. For a longer description please read this PDF.

Header
======

The SMT-LIB2 format uses a header to tell the solver which type of
problem is coming, the header needed is:

::

    (set-logic QF_ABV)
    (set-info :smt-lib-version 2.0)

QF_BV is for bit-vector problems, QF_ABV is for bit-vector and array
problems.

Declarations
============

Bit-vector expressions (or terms) are constructed out of bit-vector
constants, bit-vector variables and the functions listed below. In STP
all variables have to declared before the point of use. An example
declaration of a bit-vector variable of length, say 32, is as follows:

::

    (declare-fun x () (_ BitVec 32))

An example of an array declaration with 32 bit indices, and 7 bit
results is:

::

    (declare-fun a () (Array (_ BitVec 32) (_ BitVec 7)))

Functions and Terms
===================

Bit-vector variables (or terms) of length 0 are not allowed. Bit-vector
constants can be represented in binary or hexadecimal format. The
rightmost bit is called the least significant bit (LSB), and the
leftmost bit is the most significant bit(MSB). The index of the LSB is
0, and the index of the MSB is n-1 for an n-bit constant. This
convention naturally extends to all bit-vector expressions. Following
are some examples of bit-vector constants:

::

    #b0000111101010000, and the corresponding hex representation is #x0f50.

The Bit-vector implementation in STP supports a very large number of
functions and predicates. The functions are categorized into word-level
functions, bitwise functions, and arithmetic functions. Let t1,t2,…,tm
denote some arbitrary bitvector terms.

.. raw:: html

   <h3>

Word level functions

.. raw:: html

   </h3>

===========

.. raw:: html

   <table class="zab1">

.. raw:: html

   <tr>

.. raw:: html

   <th>

Name

.. raw:: html

   </th>

.. raw:: html

   <th>

Symbol

.. raw:: html

   </th>

.. raw:: html

   <th>

Example

.. raw:: html

   </th>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

Concatenation

.. raw:: html

   </td>

.. raw:: html

   <td>

concat

.. raw:: html

   </td>

.. raw:: html

   <td>

(concat (\_ bv0 16) x)

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

Extraction

.. raw:: html

   </td>

.. raw:: html

   <td>

extract

.. raw:: html

   </td>

.. raw:: html

   <td>

((\_ extract 7 0) o277135888)

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

left shift

.. raw:: html

   </td>

.. raw:: html

   <td>

bvlshl

.. raw:: html

   </td>

.. raw:: html

   <td>

(bvlshl x y)

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

right shift

.. raw:: html

   </td>

.. raw:: html

   <td>

bvlshr

.. raw:: html

   </td>

.. raw:: html

   <td>

(bvlshr x y)

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

sign extension

.. raw:: html

   </td>

.. raw:: html

   <td>

sign_extend

.. raw:: html

   </td>

.. raw:: html

   <td>

((\_ sign_extend 24) x)

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

Array READ

.. raw:: html

   </td>

.. raw:: html

   <td>

select

.. raw:: html

   </td>

.. raw:: html

   <td>

(select e829 v817)

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

Array WRITE

.. raw:: html

   </td>

.. raw:: html

   <td>

store

.. raw:: html

   </td>

.. raw:: html

   <td>

(store a x y)

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   </table>

Notes: \* For extraction terms, say ((_extract i j) t), n > i >= j >= 0,
where n is the length of t. \* For left shift terms, t << k is equal to
k 0’s appended to t. The length of t << k is n. \* For right shift
terms, say t >> k, the term is equal to the bitvector obtained by k 0’s
followed by t[n-1:k]. The length of t >> k is n.

.. raw:: html

   <h3>

Bitwise functions

.. raw:: html

   </h3>

===========

.. raw:: html

   <table class="zab1">

.. raw:: html

   <tr>

.. raw:: html

   <th>

Name

.. raw:: html

   </th>

.. raw:: html

   <th>

Symbol

.. raw:: html

   </th>

.. raw:: html

   <th>

Example

.. raw:: html

   </th>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

Bitwise AND

.. raw:: html

   </td>

.. raw:: html

   <td>

bvand

.. raw:: html

   </td>

.. raw:: html

   <td>

(bvand o1 o6)

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

Bitwise OR

.. raw:: html

   </td>

.. raw:: html

   <td>

bvor

.. raw:: html

   </td>

.. raw:: html

   <td>

(bvor var29 var30)

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

Bitwise NOT

.. raw:: html

   </td>

.. raw:: html

   <td>

bvnot

.. raw:: html

   </td>

.. raw:: html

   <td>

(bvnot (\_ bv0 2000))

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   <tr>

.. raw:: html

   <td>

Bitwise XOR

.. raw:: html

   </td>

.. raw:: html

   <td>

bvxor

.. raw:: html

   </td>

.. raw:: html

   <td>

(bvxor e7015 e7019)

.. raw:: html

   </td>

.. raw:: html

   </tr>

.. raw:: html

   </table>

The arguments of bitwise functions have the same length.

Footer
======

After defining the problem, tell STP what to do. Usually this is to
check the satisfiability, then to exit:

::

    (check-sat)
    (exit)

Examples
========

There are many SMT-LIB2 format examples in STP’s source code repository.
Look for files with a .smt2 extension here. Signed division of -1/-2 =
0, should be satisfiable:

::

    (set-logic QF_BV)
    (set-info :smt-lib-version 2.0)
    (set-info :status sat)
    (assert (= (bvsdiv (_ bv3 2) (_ bv2 2)) (_ bv0 2)))
    (check-sat)
    (exit)
