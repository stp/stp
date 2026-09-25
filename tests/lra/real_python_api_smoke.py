#!/usr/bin/env python3
"""Exact-Real Python construction, solve, model, and lifetime smoke."""

import gc
import weakref

from stp import ExactRealValue, Expr, RealExpr, Solver


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


solver = Solver()
require(solver.has_real_construction(), "Real construction capability")
require(solver.has_qf_lra(), "QF_LRA semantic capability")

x, y = solver.reals("x y")
half_decimal = solver.realval("0.5000")
half_fraction = solver.realval(2, 4)
linear = 3 * x + half_decimal - y / "7/9"
predicate = linear <= half_fraction

require(isinstance(x, RealExpr), "Real variable wrapper")
require(isinstance(linear, RealExpr), "Real arithmetic wrapper")
require(isinstance(predicate, Expr), "Boolean comparison wrapper")
require(linear.width is None and predicate.width is None,
        "mathematical Real/Boolean wrappers expose no BV width")

for approximate in (0.5, True):
    try:
        solver.realval(approximate)
    except TypeError as failure:
        require("floating-point values are not accepted" in str(failure),
                "approximate-number rejection diagnostic")
    else:
        raise AssertionError("approximate Python Real input was accepted")

# A product of two concrete operands is a constant, not a nonlinear term:
# it folds, here as everywhere else, and the result stays concrete, so it
# can still be the coefficient of a further product.
folded = solver.realval(2) * solver.realval(3)
require(isinstance(folded, RealExpr), "folded concrete product wrapper")
require(isinstance(folded * x, RealExpr),
        "a folded product is usable as a coefficient")

for unsupported, diagnostic in (
        (lambda: x * y, "an exact concrete coefficient"),
        (lambda: x / y, "exact concrete divisor"),
        (lambda: 1 / x, "exact concrete divisor")):
    try:
        unsupported()
    except TypeError as failure:
        require(diagnostic in str(failure),
                "unsupported Python Real operation diagnostic")
    else:
        raise AssertionError("unsupported Python Real operation was accepted")

second = Solver()
foreign = second.real("foreign")
try:
    _ = x + foreign
except ValueError as failure:
    require("different solvers" in str(failure), "cross-manager diagnostic")
else:
    raise AssertionError("cross-manager Real construction was accepted")

try:
    solver.ite(predicate, x, y)
except TypeError as failure:
    require("Real-term ite" in str(failure), "Real ite diagnostic")
else:
    raise AssertionError("unsupported Real-term ite was accepted")


def expression_from_temporary_solver():
    temporary = Solver()
    retained_solver = weakref.ref(temporary)
    value = temporary.real("lifetime") + temporary.realval("1/3")
    return value, retained_solver


retained_expression, retained_solver = expression_from_temporary_solver()
gc.collect()
require(retained_solver() is not None,
        "RealExpr did not retain its owning solver")
require(isinstance(retained_expression + "2/3", RealExpr),
        "retained RealExpr was unusable after local solver lifetime ended")

solver.add(x == solver.realval("4/3"), predicate)
require(solver.check(), "Python exact Real solve")
require(solver.has_real_model(), "Python current exact Real model")
x_value = solver.model(expr=x)
sum_value = solver.real_model_value(expr=3 * x + solver.realval("1/3"))
require(isinstance(x_value, ExactRealValue), "Python exact value wrapper")
require(x_value.canonical_fraction == "4/3" and
        x_value.numerator == "4" and x_value.denominator == "3" and
        x_value.smtlib == "(/ 4 3)", "Python exact value fields")
require(sum_value.canonical_fraction == "13/3",
        "Python normalized-expression model value")
whole_model = solver.model()
require(isinstance(whole_model["x"], ExactRealValue) and
        whole_model["x"] == x_value,
        "Python complete model did not retain exact Real values")
require("(define-fun |x| () Real (/ 4 3))" in
        solver.real_model_smtlib(), "Python legal SMT-LIB model")

try:
    x_value.numerator = "5"
except AttributeError:
    pass
else:
    raise AssertionError("Python exact value was mutable")

solver.push()
require(not solver.has_real_model(), "Python push invalidation")
solver.add(x > solver.realval("2"))
require(not solver.check(), "Python nested UNSAT")
require(not solver.has_real_model(), "Python UNSAT model invalidation")
solver.pop()
require(solver.check(), "Python post-pop repeated SAT")
require(solver.model(key="x").canonical_fraction == "4/3",
        "Python deterministic repeated exact model")

# Positional check expressions are one-call assumptions in this binding.
require(solver.check(x == solver.realval("4/3")),
        "Python SAT one-call Real assumption")
require(not solver.check(x > solver.realval("2")),
        "Python UNSAT one-call Real assumption")
require(not solver.has_real_model(),
        "Python UNSAT assumption retained an exact model")
require(solver.check() and solver.model(key="x") == x_value,
        "Python assumption state survived its public call")
require(x_value.canonical_fraction == "4/3",
        "copied Python exact DTO changed after model invalidation")

timeout_solver = Solver()
t = timeout_solver.real("t")
zero = timeout_solver.realval("0")
one = timeout_solver.realval("1")
timeout_solver.add(timeout_solver.or_(
    timeout_solver.and_(t < zero, t >= zero),
    timeout_solver.and_(t > one, t <= one)))
require(timeout_solver.check_with_timeout(max_time=0) == 3,
        "Python public zero-timeout path did not stop")
require(not timeout_solver.has_real_model(),
        "Python timeout published a stale exact model")

# The binding owns every C expression handle until deterministic solver
# teardown.  Context exit closes the checker, retained wrappers fail safely,
# and repeated close is harmless.
with Solver() as scoped_solver:
    scoped_real = scoped_solver.real("scoped")
    scoped_solver.add(scoped_real == scoped_solver.realval("5/7"))
    require(scoped_solver.check(), "Python context-managed exact Real solve")
try:
    _ = scoped_real + "1"
except RuntimeError as failure:
    require("closed" in str(failure), "closed-solver diagnostic")
else:
    raise AssertionError("expression used a closed Python solver")
scoped_solver.close()

retained_owner = retained_solver()
require(retained_owner is not None, "retained expression owner disappeared")
for owned_solver in (solver, second, timeout_solver, retained_owner):
    owned_solver.close()
    owned_solver.close()

print("PASS real-python-api-smoke")
