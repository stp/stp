# AUTHORS: Andrew Teylu
#
# BEGIN DATE: September, 2026
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

"""Exact Real arithmetic from the stp Python package: construction, the
refusals that keep it linear, solving, exact model values, scopes,
assumptions, a zero time budget and term lifetimes.

A plain script: every check runs in order and the first failure raises.
Where the package behaves differently from the 2.x ctypes binding this
smoke test was first written for, the check says what it does."""

import gc
import weakref
from fractions import Fraction

import stp as stp_package
from stp import (And, Or, If, Real, Reals, RealVal, Solver, TermManager, is_bool, is_real,
                 sat, unknown, unsat, NoModel, SortMismatch, StateError, Unsupported,
                 UnknownReason)


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


def refused(action, error_type, fragment, detail):
    try:
        action()
    except error_type as failure:
        require(fragment in str(failure), "%s: the diagnostic %r lacks %r" % (detail, str(failure), fragment))
    else:
        raise AssertionError(detail + " was accepted")


require(stp_package.capabilities().get("lra") is True, "linear Real arithmetic capability")

# construction
x, y = Reals("x y")
half_decimal = RealVal("0.5000")
half_fraction = RealVal(Fraction(2, 4))
linear = 3 * x + half_decimal - y / "7/9"
predicate = linear <= half_fraction
require(is_real(x) and is_real(linear), "Real terms")
require(is_bool(predicate), "a Real comparison is a Boolean term")
require(half_decimal.as_fraction() == Fraction(1, 2) and half_decimal is half_fraction,
        "the same value, however it is spelled, is the same term")

for approximate in (0.5, True):
    refused(lambda: RealVal(approximate), TypeError, "RealVal", "an approximate or Boolean Real value")

folded = RealVal(2) * RealVal(3)
require(folded.as_fraction() == 6, "a product of values folds")
require(is_real(folded * x), "a folded product is usable as a coefficient")

# the arithmetic stays linear, and a divisor is a non-zero value
refused(lambda: x * y, Unsupported, "must be linear", "a product of two variables")
refused(lambda: x / y, Unsupported, "divisor", "division by a variable")
refused(lambda: 1 / x, Unsupported, "divisor", "a variable divisor")

# a term belongs to its manager
foreign = Real("foreign", tm=TermManager())
refused(lambda: x + foreign, SortMismatch, "another term manager", "a term of another manager")

# 3.x: an ite over Reals is a Real term, and is decided
choice = If(predicate, x, y)
require(is_real(choice), "a Real ite")


# a term keeps its manager alive
def term_of_a_temporary_manager():
    temporary = TermManager()
    return Real("lifetime", tm=temporary) + RealVal("1/3", tm=temporary), weakref.ref(temporary)


retained, manager_ref = term_of_a_temporary_manager()
gc.collect()
require(manager_ref() is not None, "a term did not keep its manager alive")
require(is_real(retained + "2/3"), "a term of a manager no name holds is still usable")

# solving and exact values
solver = Solver()
solver.add(x == RealVal("4/3"), predicate)
require(solver.check() == sat, "an exact Real solve")
model = solver.model()
x_value = model[x]
require(x_value.as_fraction() == Fraction(4, 3), "the exact value of x")
require(model.eval(3 * x + RealVal("1/3")).as_fraction() == Fraction(13, 3),
        "the value of a term built from x")
require("(define-fun x () Real (/ 4 3))" in model.sexpr(), "the model as SMT-LIB")

# scopes
solver.push()
solver.add(x > 2)
require(solver.check() == unsat, "unsat inside a scope")
refused(solver.model, NoModel, "", "a model after an unsat check")
solver.pop()
require(solver.check() == sat and solver.model()[x].as_fraction() == Fraction(4, 3),
        "the same answer after the pop")

# assumptions hold for one check
require(solver.check(x == RealVal("4/3")) == sat, "sat under a Real assumption")
require(solver.check(x > 2) == unsat, "unsat under a Real assumption")
refused(solver.model, NoModel, "", "a model after an unsat check under assumptions")
require(solver.check() == sat and solver.model()[x] is x_value,
        "an assumption does not outlive its check")
# a model is a snapshot: the value read before is unchanged
require(x_value.as_fraction() == Fraction(4, 3), "an earlier model value")

# a zero time budget gives up at once, with no model
t = Real("t")
timed = Solver()
timed.add(Or(And(t < 0, t >= 0), And(t > 1, t <= 1)))
require(timed.check(timeout=0) == unknown, "a zero time budget did not stop the check")
require(timed.reason_unknown() == UnknownReason.TIMEOUT, "the reason is the time budget")
refused(timed.model, NoModel, "", "a model after a check that gave up")

# 3.x: terms belong to the manager, so closing a solver leaves them usable;
# the closed solver refuses every call, and closing twice is harmless
scoped = Solver()
s_real = Real("scoped")
scoped.add(s_real == RealVal("5/7"))
require(scoped.check() == sat, "a solve before closing")
scoped.close()
scoped.close()
refused(scoped.check, StateError, "closed", "a check on a closed solver")
require(is_real(s_real + "1"), "a term outlives the solver it was asserted in")

print("PASS real-python-api-smoke")
