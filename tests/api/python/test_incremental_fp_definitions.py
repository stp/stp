"""Exercise native permanent FP definitions across incremental solver states."""

import pytest
import stp


def solver(tm, enabled=True):
    """Create a checked incremental solver with optional FP definitions."""
    return stp.Solver(
        tm=tm, incremental="on", incremental_fp_definitions=enabled, check_sanity=True
    )


@pytest.mark.parametrize("enabled", [False, True])
def test_unused_guard_and_later_assumptions(enabled):
    """Defer an unused FP guard and recover its value on every later check."""
    tm = stp.TermManager()
    x = stp.FP("x", stp.Float32(tm))
    guard = stp.BitVec("guard", 1, tm=tm)
    value = stp.fpAdd(stp.RNE(tm), x, stp.FPVal(1, stp.Float32(tm)))
    definition = guard == stp.If(
        stp.fpGT(value, stp.FPVal(3, stp.Float32(tm))),
        stp.BitVecVal(1, 1, tm=tm),
        stp.BitVecVal(0, 1, tm=tm),
    )
    s = solver(tm, enabled)
    s.add(definition)
    assert s.check() == stp.sat
    first = s.model()
    assert stp.is_true(first.eval(definition))
    for input_value in [0, 4, -10, 4]:
        expected = int(input_value + 1 > 3)
        assert (
            s.check(x == stp.FPVal(input_value, stp.Float32(tm)), guard == expected)
            == stp.sat
        )
        assert s.model()[guard].as_long() == expected
        assert (
            s.check(x == stp.FPVal(input_value, stp.Float32(tm)), guard != expected)
            == stp.unsat
        )
    assert stp.is_true(first.eval(definition))


@pytest.mark.parametrize("enabled", [False, True])
def test_late_definition_frozen_symbol_and_pop(enabled):
    """Keep previously encoded symbols constrained when a definition arrives."""
    tm = stp.TermManager()
    x = stp.FP("x", stp.Float32(tm))
    g = stp.BitVec("g", 8, tm=tm)
    h = stp.BitVec("h", 8, tm=tm)
    s = solver(tm, enabled)
    s.add(stp.UGT(g, 0))
    assert s.check() == stp.sat
    s.add(
        g
        == stp.If(
            stp.fpGT(x, stp.FPVal(0, stp.Float32(tm))),
            stp.BitVecVal(1, 8, tm=tm),
            stp.BitVecVal(0, 8, tm=tm),
        )
    )
    s.add(h == g)
    assert s.check(x == stp.FPVal(-1, stp.Float32(tm))) == stp.unsat
    s.push()
    s.add(x == stp.FPVal(2, stp.Float32(tm)))
    assert s.check(h == 1) == stp.sat
    s.pop()
    assert s.check(x == stp.FPVal(3, stp.Float32(tm)), h == 1) == stp.sat
    s.reset_assertions()
    assert s.check(x == stp.FPVal(-1, stp.Float32(tm)), g == 0) == stp.sat


@pytest.mark.parametrize("enabled", [False, True])
def test_partial_conversion_and_symbolic_rounding_mode(enabled):
    """Preserve totalisation and rounding-mode constraints in defined terms."""
    tm = stp.TermManager()
    fp = stp.Float32(tm)
    x = stp.FP("x", fp)
    rm = stp.Const("rm", stp.RoundingModeSort(tm))
    b = stp.BitVec("b", 8, tm=tm)
    s = solver(tm, enabled)
    conversion = stp.fpToUBV(rm, x, 8)
    s.add(b == conversion)
    assert s.check() == stp.sat
    assert stp.is_true(s.model().eval(b == conversion))
    assert s.check(x == stp.FPVal(3, fp), b != 3) == stp.unsat
    assert s.check(stp.fpIsNaN(x), b == 37) == stp.sat
    assert s.model()[b].as_long() == 37
    assert stp.is_true(s.model().eval(b == conversion))


@pytest.mark.parametrize("enabled", [False, True])
def test_fp_definition_used_as_array_index(enabled):
    """Classify array uses after substituting a permanent FP-derived index."""
    tm = stp.TermManager()
    x = stp.FP("x", stp.Float32(tm))
    index = stp.BitVec("index", 2, tm=tm)
    array = stp.Array("a", stp.BitVecSort(2, tm=tm), stp.BitVecSort(8, tm=tm))
    s = solver(tm, enabled)
    s.add(
        index
        == stp.If(
            stp.fpIsNaN(x), stp.BitVecVal(0, 2, tm=tm), stp.BitVecVal(1, 2, tm=tm)
        )
    )
    s.add(stp.Select(array, index) == 17)
    assert s.check(stp.fpIsNaN(x), stp.Select(array, 0) != 17) == stp.unsat
    assert s.check(stp.Not(stp.fpIsNaN(x)), stp.Select(array, 1) != 17) == stp.unsat
    assert s.check(stp.Select(array, index) == 17) == stp.sat


@pytest.mark.parametrize("enabled", [False, True])
def test_definition_cycle_and_fp_value_model(enabled):
    """Reject cyclic substitutions and reconstruct eliminated FP values."""
    tm = stp.TermManager()
    fp = stp.Float32(tm)
    x, y = stp.FP("x", fp), stp.FP("y", fp)
    a, b = stp.BitVec("a", 8, tm=tm), stp.BitVec("b", 8, tm=tm)
    s = solver(tm, enabled)
    s.add(a == stp.If(stp.fpIsNaN(x), b, stp.BitVecVal(0, 8, tm=tm)))
    s.add(b == a + 1)
    s.add(y == stp.fpAdd(stp.RNE(tm), x, stp.FPVal(1, fp)))
    assert s.check(stp.fpIsNaN(x)) == stp.unsat
    assert s.check(x == stp.FPVal(2, fp)) == stp.sat
    model = s.model()
    assert model[a].as_long() == 0 and model[b].as_long() == 1
    assert model[y].bits() == stp.FPVal(3, fp).bits()


@pytest.mark.parametrize("enabled", [False, True])
def test_late_definition_of_encoded_fp_symbol(enabled):
    """Retain an FP symbol's encoded constraints when its definition arrives."""
    tm = stp.TermManager()
    fp = stp.Float32(tm)
    x, y = stp.FP("x", fp), stp.FP("y", fp)
    s = solver(tm, enabled)
    positive = stp.fpGT(y, stp.FPVal(0, fp))
    s.add(positive)
    assert s.check() == stp.sat
    first = s.model()
    s.add(y == stp.fpAdd(stp.RNE(tm), x, stp.FPVal(1, fp)))
    assert s.check(x == stp.FPVal(-2, fp)) == stp.unsat
    assert s.check(x == stp.FPVal(2, fp)) == stp.sat
    assert s.model()[y].bits() == stp.FPVal(3, fp).bits()
    assert stp.is_true(first.eval(positive))


@pytest.mark.parametrize("enabled", [False, True])
def test_signed_zero_and_nan_in_reconstructed_definition(enabled):
    """Preserve zero signs and NaN classification in an eliminated FP value."""
    tm = stp.TermManager()
    fp = stp.Float32(tm)
    x, y = stp.FP("x", fp), stp.FP("y", fp)
    s = solver(tm, enabled)
    definition = y == stp.fpNeg(x)
    s.add(definition)
    for value in (0.0, -0.0):
        assert s.check(x == stp.FPVal(value, fp)) == stp.sat
        assert s.model()[y].bits() == stp.FPVal(-value, fp).bits()
        assert stp.is_true(s.model().eval(definition))
    assert s.check(stp.fpIsNaN(x), stp.Not(stp.fpIsNaN(y))) == stp.unsat
    assert s.check(stp.fpIsNaN(x), stp.fpIsNaN(y)) == stp.sat


@pytest.mark.parametrize("enabled", [False, True])
def test_new_definition_after_previous_checks(enabled):
    """Expand newly defined operands after earlier checks used their symbols."""
    tm = stp.TermManager()
    a, b, c = [stp.BitVec(name, 8, tm=tm) for name in ("a", "b", "c")]
    s = solver(tm, enabled)
    s.add(a == b + 1)
    assert s.check(a == 10) == stp.sat
    first = s.model()
    s.add(b == c + 2)
    assert s.check(c == 3, a != 6) == stp.unsat
    assert s.check(c == 3, a == 6) == stp.sat
    s.push()
    s.add(c == 5)
    assert s.check(a == 8) == stp.sat
    s.pop()
    assert s.check(c == 4, a == 7) == stp.sat
    assert first[a].as_long() == 10
