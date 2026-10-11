"""Keep batch term construction equivalent to individual checked calls."""

import pytest
import stp


def test_dependencies_identity_and_evaluation():
    """Resolve earlier results and reuse canonical wrappers for equal nodes."""
    tm = stp.TermManager()
    x = stp.BitVec("batch_x", 8, tm=tm)
    one = stp.BitVecVal(1, 8, tm=tm)
    terms = tm.mk_terms(
        [
            (stp.Kind.BV_ADD, [x, one]),
            (stp.Kind.BV_MUL, [0, 0]),
            (stp.Kind.EQUAL, [1, x]),
            (stp.Kind.BV_ADD, [x, one]),
        ]
    )
    assert terms[0] is terms[3]
    assert terms[0] is tm.mk_term(stp.Kind.BV_ADD, [x, one])
    assert terms[1] is tm.mk_term(stp.Kind.BV_MUL, [terms[0], terms[0]])
    solver = stp.Solver(tm=tm)
    assert solver.check(x == 7) == stp.sat
    assert solver.model().eval(terms[1]).as_long() == 64
    assert not stp.is_true(solver.model().eval(terms[2]))


def test_indices_sorts_and_mixed_theories():
    """Preserve indexed operations, constant arrays, FP, Real and UF terms."""
    tm = stp.TermManager()
    bv = stp.BitVecSort(8, tm=tm)
    array_sort = stp.ArraySort(bv, bv)
    x = stp.BitVec("batch_bits", 8, tm=tm)
    fp = stp.FP("batch_fp", stp.Float32(tm))
    real = stp.Real("batch_real", tm=tm)
    function = stp.Function("batch_f", bv, bv)
    operations = [
        (stp.Kind.BV_EXTRACT, [x], ("7", "0"), None),
        (stp.Kind.CONST_ARRAY, [0], (), array_sort),
        (stp.Kind.SELECT, [1, x]),
        (stp.Kind.APPLY, [function, 2]),
        (stp.Kind.FP_ADD, [stp.RNE(tm), fp, fp]),
        (stp.Kind.REAL_ADD, [real, real]),
    ]
    terms = tm.mk_terms(operations)
    assert terms[0] is x
    assert terms[2] is tm.mk_term(stp.Kind.SELECT, [terms[1], x])
    assert terms[3] is function(terms[2])
    assert terms[4] is stp.fpAdd(stp.RNE(tm), fp, fp)
    assert terms[5] is real + real
    solver = stp.Solver(tm=tm)
    assert solver.check(x == 15, terms[2] != 15) == stp.unsat


@pytest.mark.parametrize("reference", [-1, 0, 8])
def test_invalid_reference_is_rejected(reference):
    """Reject forward and negative references without retaining an error."""
    tm = stp.TermManager()
    with pytest.raises(ValueError, match="earlier result"):
        tm.mk_terms([(stp.Kind.NOT, [reference])])
    assert tm.mk_terms([]) == []
    assert tm.pending_error() is None


@pytest.mark.parametrize("operand", [True, None, "x", object()])
def test_non_term_arguments_are_rejected(operand):
    """Reject literals and arbitrary objects in the term argument positions."""
    with pytest.raises(TypeError, match="term argument"):
        stp.TermManager().mk_terms([(stp.Kind.NOT, [operand])])


def test_foreign_manager_and_constructor_validation():
    """Apply the same ownership, arity, index and sort checks as mk_term."""
    tm = stp.TermManager()
    x = stp.BitVec("batch_local", 8, tm=tm)
    foreign = stp.BitVec("batch_foreign", 8, tm=stp.TermManager())
    with pytest.raises(stp.SortMismatch):
        tm.mk_terms([(stp.Kind.BV_ADD, [x, foreign])])
    for operation in (
        (stp.Kind.BV_ADD, [x]),
        (stp.Kind.BV_EXTRACT, [x], (10, 0), None),
        (stp.Kind.BV_ADD, [x, stp.BoolVal(True, tm=tm)]),
    ):
        with pytest.raises(stp.Error):
            tm.mk_terms([operation])
        assert tm.pending_error() is None
    assert tm.mk_terms([(stp.Kind.BV_ADD, [x, x])])[0] is x + x


def test_iterables_and_failure_after_valid_nodes():
    """Accept input iterables and remain usable after a later operation fails."""
    tm = stp.TermManager()
    x = stp.BitVec("batch_iterable", 8, tm=tm)
    operations = [(stp.Kind.BV_ADD, iter([x, x])), (stp.Kind.BV_MUL, iter([0, x]))]
    terms = tm.mk_terms(iter(operations))
    assert terms[1] is (x + x) * x
    with pytest.raises(ValueError):
        tm.mk_terms([(stp.Kind.BV_ADD, [x, x]), (stp.Kind.BV_ADD, [0, 3])])
    assert tm.mk_terms([(stp.Kind.BV_ADD, [x, x])])[0] is terms[0]
