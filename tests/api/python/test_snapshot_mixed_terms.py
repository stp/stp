"""Preserve partial FP choices and Real UF cases in detached snapshots."""

import pytest

from stp import (
    FP,
    Float32,
    Function,
    RNE,
    Real,
    RealSort,
    Solver,
    fpNaN,
    fpToUBV,
    sat,
)


@pytest.mark.parametrize("mode", ["auto", "on", "off"])
def test_partial_fp_and_real_function_survive_later_checks(mode):
    """Retain both theories' choices after replacing the check assumptions."""
    x = FP("snapshot_mixed_x", Float32())
    r = Real("snapshot_mixed_r")
    f = Function("snapshot_mixed_f", RealSort(), RealSort())
    partial = fpToUBV(RNE(), x, 8)
    solver = Solver(incremental=mode)
    solver.add(x == fpNaN(Float32()), r == 2)
    assert solver.check(partial == 3, f(r) == 7) == sat
    first = solver.model()
    assert solver.check(partial == 5, f(r) == 9) == sat
    second = solver.model()
    solver.close()
    for model, bv_value, real_value in ((first, 3, 7), (second, 5, 9)):
        assert model.eval(partial).as_long() == bv_value
        assert model.eval(f(r)).as_fraction() == real_value
        assert model.eval(f(2)).as_fraction() == real_value
