from stp import Solver

if __name__ == '__main__':
    s = Solver()
    a = s.bitvec('a', 32)
    b = s.bitvec('b', 32)
    c = s.bitvecval(32, 1337)
    d = s.bitvecval(32, 42)
    if not s.check(b.eq(d), a.add(b).eq(c)):
        print 'Nope..'
    else:
        print s.model()
