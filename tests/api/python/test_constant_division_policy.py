"""Exercise the public crossover option and both exact division encodings."""

import pytest

from stp import BitVec, Options, Solver, TermManager, UDiv, URem, sat, unsat


def test_public_constant_division_default_and_override():
    options = Options()
    assert options.info("bb.div-by-const-width").default == 128
    assert options["bb_div_by_const_width"] == 128
    options["bb_div_by_const_width"] = 64
    assert options["bb.div-by-const-width"] == 64


@pytest.mark.parametrize("width", [97, 127, 128])
@pytest.mark.parametrize("crossover", [None, 64, 256])
def test_constant_division_models_and_incremental_remainder(width, crossover):
    options = dict(incremental="on", max_time=5000)
    if crossover is not None:
        options["bb_div_by_const_width"] = crossover
    term_manager = TermManager(simplify=False)
    dividend = BitVec("dividend", width, tm=term_manager)
    quotient, remainder = UDiv(dividend, 11), URem(dividend, 11)
    solver = Solver(tm=term_manager, **options)
    try:
        solver.add(quotient == 17)
        solver.push()
        solver.add(remainder == 5)
        assert solver.check() == sat
        model = solver.model()
        assert model.eval(dividend).as_long() == 17 * 11 + 5
        assert model.eval(quotient).as_long() == 17
        assert model.eval(remainder).as_long() == 5
        solver.pop()
        solver.push()
        solver.add(remainder == 11)
        assert solver.check() == unsat
        solver.pop()
        assert solver.check() == sat
    finally:
        solver.close()
