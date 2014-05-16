#!/usr/bin/env python
"""
The MIT License

Copyright (c) 2008 Vijay Ganesh
              2014 Jurriaan Bremer, jurriaanbremer@gmail.com

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
"""

from stp import stp, Solver
import unittest


@stp
def test0_foo(a, b):
    assert b != 0
    return (a + 42) % b


@stp
def test0_bar(a, b):
    return a * b == 12345


class TestSTP(unittest.TestCase):
    def setUp(self):
        self.s = Solver()

    def test_simple(self):
        s = self.s
        a = s.bitvec('a', 32)
        b = s.bitvec('b', 32)
        c = s.bitvecval(32, 1337)
        d = s.bitvecval(32, 42)
        self.assertTrue(s.check(b.eq(d), a.add(b).eq(c)))
        self.assertEqual(s.model(), {'a': 1337-42, 'b': 42})

    def test_bitvecval(self):
        s = self.s
        a = s.bitvec('a', 32)
        b = s.bitvec('b', 32)
        self.assertTrue(s.check(a.add(b).eq(69)))
        self.assertEqual(s.model()['a'] + s.model()['b'], 69)

    def test_operator(self):
        s = self.s
        a = s.bitvec('a', 32)
        b = s.bitvec('b', 32)
        c = s.bitvec('c', 32)
        self.assertTrue(s.check(a + b + c == 123, b - c == 66))
        m = s.model()
        self.assertEqual((m['a']+m['b']+m['c'])%2**32, 123)
        self.assertEqual(m['b']-m['c'], 66)

        d = s.bitvec('d', 32)
        self.assertTrue(s.check((a << 1) - d == b))
        m = s.model()
        self.assertEqual((m['a'] << 1) - m['d'], b)

    def test_quick_model(self):
        s = self.s
        a = s.bitvec('a', 32)
        b = s.bitvec('b', 32)
        c = s.bitvec('c', 32)
        self.assertTrue(s.check(a + b + c == 666, b - c == 321, c != 666))
        self.assertEqual((s['a'] + s['b'] + s['c'])%2**32, 666)
        self.assertEqual((s['b'] - s['c'])%2**32, 321)

    def test_bitvec32(self):
        s = self.s
        a, b, c = s.bitvecs('a b c')
        s.add(a != 0, b != 0, c != 0, a != b, b != c, a != c)
        self.assertTrue(s.check(a * 2 + b * 2 == c * 2))
        self.assertEqual((s['a'] * 2 + s['b'] * 2)%2**32, s['c'] * 2 % 2**32)

    def test_boolean_expr(self):
        s = self.s
        a, b, c = s.bitvecs('a b c')
        s.add(a != b, a != c, b != c)
        self.assertTrue(s.check(s.or_(a + b == 1, a + c == 1)))
        self.assertTrue(s['a'] + s['b'] == 1 or s['a'] + s['c'] == 1)

    def test_ast(self):
        models = [
            {'y': 1658330539, 'x': 1658330539},
            {'y': 3805814187, 'x': 3805814187},
            {'y': 2636636757, 'x': 2636636757},
            {'y': 489153109, 'x': 489153109},
        ]

        with Solver() as s:
            x, y = s.bitvecs('x y')
            count = 0
            while s.check(test0_foo(x, y) == test0_foo(y, x),
                          test0_bar(x, y)):
                count += 1
                assert s.model() in models
                s.add(x != s.model('x'))

            assert count == 4

    def test_value(self):
        s = self.s
        a = s.bitvec('a')
        s.check(a == 0x41414141)
        self.assertEqual(a.value, 0x41414141)

    def test_pushpop(self):
        s = self.s

        s.push()
        # .add is permanent - once an expression has been added, it cannot
        # be contradicted.
        a = s.bitvec('a')
        s.add(a == 2)
        self.assertTrue(s.check())
        self.assertEqual(s.model(), {'a': 2})

        # Contradicts the earlier .add formula.
        self.assertFalse(s.check(a == 3))

        # Contradicts the earlier .add formula.
        s.add(a == 3)
        self.assertFalse(s.check())
        s.pop()

        s.push()
        # .check is only used in the current query - an expression given
        # to .check is not persistent, and can contradict any earlier
        # expression that has been given to .check.
        b = s.bitvec('b')
        self.assertTrue(s.check(b == 1))
        self.assertTrue(s.check(b == 2))
        s.pop()

    def test_reflected(self):
        # Reflected/swapped stuff is like "y+x" instead of "x+y" where "y"
        # is not an Expr instance, e.g., a plain integer.
        s = self.s

        a, b = s.bitvecs('a b')
        self.assertTrue(s.check(42 == a))
        self.assertEqual(s['a'], 42)

        self.assertTrue(s.check(456 == 123 + a))
        self.assertEqual(s['a'], 456-123)


if __name__ == '__main__':
    unittest.main()
