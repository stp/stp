from stp import add, bitvecs, check, model, stp, Solver
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
            {'y': 1658330539L, 'x': 1658330539L},
            {'y': 3805814187L, 'x': 3805814187L},
            {'y': 2636636757L, 'x': 2636636757L},
            {'y': 489153109L, 'x': 489153109L},
        ]

        with Solver():
            x, y = bitvecs('x y')
            count = 0
            while check(test0_foo(x, y) == test0_foo(y, x), test0_bar(x, y)):
                count += 1
                assert model() in models
                add(x != model('x'))

            assert count == 4


if __name__ == '__main__':
    unittest.main()
