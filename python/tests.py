from stp import Solver
import unittest


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


if __name__ == '__main__':
    unittest.main()
