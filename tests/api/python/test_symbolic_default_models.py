"""Model snapshots retain partial FP choices hidden in array defaults."""

import pytest

from stp import (
    Array, BitVecSort, FP, Float32, K, RNE, Solver, fpNaN, fpToUBV, sat,
)


@pytest.mark.parametrize("mode", ["auto", "on", "off"])
def test_hidden_partial_conversion_keeps_the_solving_choice(mode):
    x = FP("ca_partial_fp", Float32())
    a = Array("ca_partial_array", BitVecSort(8), BitVecSort(8))
    value = fpToUBV(RNE(), x, 8)
    constant = K(BitVecSort(8), value)
    s = Solver(incremental=mode)
    # A NaN conversion may return any bitvector. This assertion selects a
    # nonzero answer, which the snapshot must retain for the default term.
    s.add(x == fpNaN(Float32()), a == constant, a[0] == 3)
    assert s.check() == sat
    model = s.model()
    assert model[a].default.as_long() == 3
    assert model.eval(constant).default.as_long() == 3
    assert model.eval(value).as_long() == 3
    assert bool(model.eval(a == constant)) is True
    s.close()
