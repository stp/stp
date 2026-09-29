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

"""stp -- the STP 3.x Python API (z3py-flavoured).

    from stp import *
    x, y = BitVecs('x y', 32)
    s = Solver()
    s.add(x * 3 == 7, y == LShR(x, 1))
    assert s.check() == sat
    m = s.model()
    print(m[x].as_long(), m[y].as_hex_string())

The classes live in the Cython extension stp._core (handles, error translation, the
GIL-free checks); this package is the pure-Python shell over it.
"""

try:
    from . import _core
except ImportError as e:  # the circular-import wording Python gives this case misleads
    import sys as _sys
    raise ImportError("stp._core could not be loaded into Python %d.%d: an extension built for another "
                      "interpreter, or one whose libstp is missing, fails this way. Build STP with "
                      "-DPYTHON_EXECUTABLE naming this interpreter, or pip install ./bindings/python "
                      "with it. (%s)" % (_sys.version_info[0], _sys.version_info[1], e)) from e
from ._core import (Error, ArgumentError, SortMismatch, DoesNotFit, NotAValue, NoModel, Unsupported,
                    OptionError, UnknownOption, ParseError, IOError, StateError, ResourceError, InternalError)
from ._gen_kinds import Kind, ErrorCode, Option
from ._terms import (
    SortKind, RoundingMode, UnknownReason, Tier,
    TermManager, main_tm, set_main_tm,
    SortRef, BoolSortRef, BitVecSortRef, FPSortRef, RMSortRef, RealSortRef, ArraySortRef, FuncSortRef,
    UninterpretedSortRef,
    BoolSort, BitVecSort, FPSort, Float16, Float32, Float64, Float128, FloatHalf, FloatSingle, FloatDouble,
    FloatQuadruple, RoundingModeSort, RealSort, ArraySort, FuncSort, DeclareSort, FreshSort,
    ExprRef, BoolRef, BoolNumRef, BitVecRef, BitVecNumRef, FPRef, FPNumRef, RMRef, RMNumRef, RealRef, RatNumRef,
    ArrayRef, ArrayNumRef, FuncRef, FuncEntry, FuncInterp, UninterpretedRef, UninterpretedNumRef,
    Bool, Bools, BoolVal, BitVec, BitVecs, BitVecVal, FP, FPs, FPVal, fpFromBits, fpNaN, fpPlusInfinity,
    fpMinusInfinity, fpInfinity, fpPlusZero, fpMinusZero, fpZero, fpFP, RNE, RNA, RTP, RTN, RTZ,
    RoundNearestTiesToEven, RoundNearestTiesToAway, RoundTowardPositive, RoundTowardNegative, RoundTowardZero,
    RMVal, Real, Reals, RealVal, Q, Array, K, ArrayFromBytes, Function, Const, Consts, FreshConst, FreshBool,
    FreshBitVec,
    And, Or, Not, Xor, Implies, If, Distinct, Sum, Product, ULT, ULE, UGT, UGE, UDiv, URem, SDiv, SRem, SMod,
    LShR, SLT, SLE, SGT, SGE, Extract, Bit, BoolToBV1, BV1ToBool, Concat, ZeroExt, SignExt, RepeatBitVec,
    RepeatBV, RotateLeft, RotateRight, BVComp, BVNand, BVNor, BVXnor, BVRedAnd, BVRedOr,
    bvuaddo, bvsaddo, bvumulo, bvsmulo, bvusubo, bvssubo, bvnego, bvsdivo,
    BVAddNoOverflow, BVAddNoUnderflow, BVSubNoOverflow, BVSubNoUnderflow, BVMulNoOverflow, BVMulNoUnderflow,
    BVSNegNoOverflow, BVSDivNoOverflow, Select, Store, Update, Default,
    fpAbs, fpNeg, fpAdd, fpSub, fpMul, fpDiv, fpFMA, fpSqrt, fpRem, fpRoundToIntegral, fpMin, fpMax, fpEQ, fpNEQ,
    fpLT, fpLEQ, fpGT, fpGEQ, fpIsNaN, fpIsInf, fpIsZero, fpIsNormal, fpIsSubnormal, fpIsNegative, fpIsPositive,
    fpToFP, fpFPToFP, fpBVToFP, fpSignedToFP, fpUnsignedToFP, fpRealToFP, fpToSBV, fpToUBV, fpToIEEEBV, fpToReal,
    simplify, substitute, is_true, is_false, is_expr, is_app, is_const, is_symbol, is_value, is_bv, is_bv_value,
    is_fp, is_fp_value, is_real, is_rational_value, is_array, is_bool, is_func_decl, is_rm, is_sort,
)
from ._solver import (
    OptionInfo, Options, CheckSatResult, sat, unsat, unknown, EntailmentResult, valid, invalid, Statistics,
    Solver, Model, SolverFor, SimpleSolver, solve, prove, parse_smt2_string, parse_smt2_file, stp,
    solver_scope, current_solver, add, check, model,
)


class Version:
    """The library version: major, minor, patch, string, git_sha, git_tag, build_info."""

    def __init__(self):
        (self.major, self.minor, self.patch, self.string, self.git_sha, self.git_tag,
         self.build_info) = _core.version()

    def __str__(self):
        return self.string

    def __repr__(self):
        return "Version(%s)" % self.string


def version():
    return Version()


__version__ = _core.version()[3]


def capabilities():
    """The library's capabilities as a dict (bools, ints, strings and comma lists parsed)."""
    out = {}
    for line in _core.capabilities().splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        v = value.strip()
        if v in ("true", "false"):
            out[key.strip()] = v == "true"
        elif v.lstrip("-").isdigit():
            out[key.strip()] = int(v)
        elif "," in v:
            out[key.strip()] = v.split(",")
        else:
            out[key.strip()] = v
    return out


def capability(key):
    return _core.capability(key)


def has_sat_backend(name):
    return _core.has_sat_backend(name)


def sat_backends():
    return _core.sat_backends()


def set_internal_error_policy(abort):
    """Process-wide: abort (True) or poison the object (False, the default) on INTERNAL/RESOURCE errors."""
    _core.set_internal_error_policy(abort)


def get_internal_error_policy():
    return _core.get_internal_error_policy()


__all__ = [
    # library
    "__version__", "version", "Version", "capabilities", "capability", "has_sat_backend", "sat_backends",
    "set_internal_error_policy", "get_internal_error_policy",
    # enums
    "Kind", "SortKind", "RoundingMode", "UnknownReason", "ErrorCode", "Tier", "Option",
    # errors
    "Error", "ArgumentError", "SortMismatch", "DoesNotFit", "NotAValue", "NoModel", "Unsupported", "OptionError",
    "UnknownOption", "ParseError", "StateError", "ResourceError", "InternalError",
    # manager
    "TermManager", "main_tm", "set_main_tm",
    # sorts
    "SortRef", "BoolSortRef", "BitVecSortRef", "FPSortRef", "RMSortRef", "RealSortRef", "ArraySortRef",
    "FuncSortRef", "UninterpretedSortRef", "BoolSort", "BitVecSort", "FPSort", "Float16", "Float32", "Float64",
    "Float128", "FloatHalf", "FloatSingle", "FloatDouble", "FloatQuadruple", "RoundingModeSort", "RealSort",
    "ArraySort", "FuncSort", "DeclareSort", "FreshSort",
    # terms
    "ExprRef", "BoolRef", "BoolNumRef", "BitVecRef", "BitVecNumRef", "FPRef", "FPNumRef", "RMRef", "RMNumRef",
    "RealRef", "RatNumRef", "ArrayRef", "ArrayNumRef", "FuncRef", "FuncEntry", "FuncInterp", "UninterpretedRef",
    "UninterpretedNumRef",
    # declarations and values
    "Bool", "Bools", "BoolVal", "BitVec", "BitVecs", "BitVecVal", "FP", "FPs", "FPVal", "fpFromBits", "fpNaN",
    "fpPlusInfinity", "fpMinusInfinity", "fpInfinity", "fpPlusZero", "fpMinusZero", "fpZero", "fpFP", "RNE", "RNA",
    "RTP", "RTN", "RTZ", "RoundNearestTiesToEven", "RoundNearestTiesToAway", "RoundTowardPositive",
    "RoundTowardNegative", "RoundTowardZero", "RMVal", "Real", "Reals", "RealVal", "Q", "Array", "K",
    "ArrayFromBytes", "Function", "Const", "Consts", "FreshConst", "FreshBool", "FreshBitVec",
    # operators
    "And", "Or", "Not", "Xor", "Implies", "If", "Distinct", "Sum", "Product", "ULT", "ULE", "UGT", "UGE", "UDiv",
    "URem", "SDiv", "SRem", "SMod", "LShR", "SLT", "SLE", "SGT", "SGE", "Extract", "Bit", "BoolToBV1", "BV1ToBool",
    "Concat", "ZeroExt", "SignExt", "RepeatBitVec", "RepeatBV", "RotateLeft", "RotateRight", "BVComp", "BVNand",
    "BVNor", "BVXnor", "BVRedAnd", "BVRedOr", "bvuaddo", "bvsaddo", "bvumulo", "bvsmulo", "bvusubo", "bvssubo",
    "bvnego", "bvsdivo", "BVAddNoOverflow", "BVAddNoUnderflow", "BVSubNoOverflow", "BVSubNoUnderflow",
    "BVMulNoOverflow", "BVMulNoUnderflow", "BVSNegNoOverflow", "BVSDivNoOverflow", "Select", "Store", "Update",
    "Default", "fpAbs", "fpNeg", "fpAdd", "fpSub", "fpMul", "fpDiv", "fpFMA", "fpSqrt", "fpRem",
    "fpRoundToIntegral", "fpMin", "fpMax", "fpEQ", "fpNEQ", "fpLT", "fpLEQ", "fpGT", "fpGEQ", "fpIsNaN", "fpIsInf",
    "fpIsZero", "fpIsNormal", "fpIsSubnormal", "fpIsNegative", "fpIsPositive", "fpToFP", "fpFPToFP", "fpBVToFP",
    "fpSignedToFP", "fpUnsignedToFP", "fpRealToFP", "fpToSBV", "fpToUBV", "fpToIEEEBV", "fpToReal", "simplify",
    "substitute", "is_true", "is_false", "is_expr", "is_app", "is_const", "is_symbol", "is_value", "is_bv",
    "is_bv_value", "is_fp", "is_fp_value", "is_real", "is_rational_value", "is_array", "is_bool", "is_func_decl",
    "is_rm", "is_sort",
    # solving
    "OptionInfo", "Options", "CheckSatResult", "sat", "unsat", "unknown", "EntailmentResult", "valid", "invalid",
    "Statistics", "Solver", "Model", "SolverFor", "SimpleSolver", "solve", "prove", "parse_smt2_string",
    "parse_smt2_file", "stp", "solver_scope", "current_solver", "add", "check", "model",
]
