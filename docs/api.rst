The 3.x API (C++, C and Python)
================================

STP 3.x replaces the ``vc_*`` interface of ``c_interface.h`` with one API
designed together for three languages: ``<stp/stp.hpp>`` for C++17,
``<stp/stp.h>`` for C, and the ``stp`` Python package (a Cython module under a
z3py-style shell). The three surfaces share one object model and one option
registry, so a program reads the same way in each. ``libstp`` carries this API
alone, and STP's own command line, bindings and tests are written against it.
The 2.x interface survives as ``libstp2``, a separate compatibility library
implemented over the C API (see :ref:`api-compat`).

Objects
-------

``TermManager``
  Owns terms and sorts. Terms are hash-consed: building the same term twice
  gives the same node. Copies of a manager handle share one manager; it lives
  while anything that came from it lives. Three settings are fixed per manager:
  whether construction folds constants (``simplify``, default on), the default
  rounding mode used by floating-point operators, and the carrier width of
  declared sorts.

``Sort`` / ``Term``
  Values, cheap to copy. A term knows its ``kind()`` (one of the 102 public
  kinds of ``kinds.toml``), its ``sort()``, its ``children()`` and ``indices()``
  (``(_ extract 7 0)`` has one child and two indices). A value term
  (``kind() == VALUE``) is decoded with typed readers: ``to_uint64``,
  ``to_bv_string(16)``, ``to_bv_limbs``, ``to_fp()``, ``to_rm()``,
  ``to_rational()``.

``Solver``
  Assertions, ``push``/``pop``, ``check_sat`` (optionally under assumptions and
  a per-check budget), ``entails``, the ``Model`` of the last satisfiable
  check, ``interrupt()`` (safe from any thread), parsing of SMT-LIB 2, SMT-LIB 1
  and CVC input, printing, statistics.

``Model``
  A detached snapshot: it survives every later assertion, push or pop, and it
  evaluates any term of its manager, including terms built after the check.
  Symbols the solver never assigned are completed with their sort's default;
  ``try_value`` refuses to complete instead.

``Options``
  The whole option registry of the ``stp`` binary, settable by name with the
  text form the command line uses, or through typed setters. Every entry has a
  tier (stable, expert, experimental, diagnostic) and a settable window
  (anytime, before the first check, at construction); a write outside the
  window is a recoverable error, never silent. The binary registers its own
  command line from the same registry, so an option has one spelling, one
  default and one meaning whether it arrives as ``--name`` or through
  ``Options::set``; the binary's only additions are its frontend switches
  (input format, printing, ``--parse-only``, ``--interactive``).

Errors are exceptions in C++ and Python and a per-manager error record in C.
Every precondition is checked in every build type; a recoverable error leaves
every object as it was. The library never calls ``exit()`` or ``abort()``: a
script the frontend refuses (a sort error, a wrong arity, a constant that
does not fit its width) is a ``PARSE`` error with the solver as it was, and an
engine failure inside any call is ``INTERNAL`` and poisons the manager, after
which every call on it, its solvers, models and terms is refused with
``STATE`` naming the failure.

C++
---

.. code-block:: cpp

   #include <stp/stp.hpp>
   using namespace stp;

   TermManager tm;
   Sort bv32 = tm.mk_bv_sort(32);
   Term x = tm.declare("x", bv32), y = tm.declare("y", bv32);

   Solver s(tm);
   s.add(x * 3 == 7);                 // literals take the term's sort and must fit
   s.add(bvult(y, 10));               // no <,> on terms: signedness is explicit
   if (s.check_sat().is_sat())
   {
     Model m = s.model();
     std::cout << m.uint64_value(x) << "\n";   // 2863311533
     std::cout << m.value(x * 3) << "\n";      // #x00000007
   }

Arrays, floating point, uninterpreted functions and Reals use the same shapes:

.. code-block:: cpp

   Sort arr = tm.mk_array_sort(bv32, tm.mk_bv_sort(8));
   Term a = tm.declare("a", arr), i = tm.declare("i", bv32);
   s.add(a[i] == 42);                 // select; store(a, i, v) for the update
   s.add(a == store(tm.declare("b", arr), i, tm.mk_bv(8, 1)));   // extensional
   s.add(a != tm.mk_const_array(arr, tm.mk_bv(8, 0)));          // ((as const ...) #x00)

   Sort f32 = tm.mk_fp32_sort();
   Term fx = tm.declare("fx", f32);
   s.add(fp_add(RoundingMode::RNE, fx, 1.0) == tm.mk_fp(f32, RoundingMode::RNE, 3.0));
   FloatValue v = s.model().fp_value(fx);     // sign, exponent, significand, class

   Term f = tm.declare("f", tm.mk_fun_sort({bv32}, bv32));
   s.add(f(x) == f(y));
   FunctionValue fv = s.model().function_value(f);

   Term r = tm.declare("r", tm.mk_real_sort());
   s.add(real_lt(r + 1, tm.mk_real("3/2")));
   RationalValue q = s.model().real_value(r);

Options are set at construction or on the live solver:

.. code-block:: cpp

   Options o;
   o.set("max-time", "2s");           // the CLI's text form, unit required
   o.set_str("sat-backend", "cadical");
   o.set_args({"--fp-abstraction", "--bb.div-v3=false"});
   Solver s(tm, o);
   s.options().set_bool("check-sanity", true);   // anytime
   Result r = s.check_sat({assumption}, CheckBudget{std::chrono::milliseconds(500), std::nullopt});
   if (r.is_unknown()) std::cout << r.reason_message();

C
-

The C header mirrors the C++ one function for function. Handles are retained
engine nodes: every returned term carries a reference that
``stp_term_release`` gives back, or that a scope (``stp_tm_scope_push`` /
``stp_tm_scope_pop``) releases in bulk. A failing call returns ``NULL`` or
``STP_ERROR`` and records the first error since ``stp_tm_clear_error`` in
the manager (``stp_tm_error``); a ``NULL`` term argument propagates without a
record so a chain of constructions can be checked once.

.. code-block:: c

   #include <stp/stp.h>

   stp_tm tm = stp_tm_new(NULL);
   stp_sort bv32 = stp_mk_bv_sort(tm, 32);
   stp_term x = stp_declare(tm, "x", bv32);
   stp_term c = stp_eq(tm, stp_bvmul(tm, x, stp_mk_bv_uint64(tm, 32, 3)),
                       stp_mk_bv_uint64(tm, 32, 7));
   stp_solver s = stp_solver_new(tm, NULL);
   stp_solver_assert(s, c);
   stp_result r;
   if (stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT)
   {
     stp_model m = stp_solver_model(s);
     uint64_t v;
     stp_model_uint64(m, x, &v);
     stp_model_release(m);
   }
   if (stp_tm_error(tm))
     fprintf(stderr, "%s\n", stp_tm_error(tm)->message);
   stp_solver_delete(s);
   stp_tm_release_all(tm);
   stp_tm_release(tm);

Python
------

The Python package is the z3py idiom over the same objects:

.. code-block:: python

   from stp import *

   x, y = BitVecs('x y', 32)
   s = Solver()
   s.add(x * 3 == 7, ULT(y, 10))
   if s.check() == sat:
       m = s.model()
       print(m[x].as_long(), m.eval(x * 3))

   a = Array('a', BitVecSort(32), BitVecSort(8))
   s.add(a[y] == 42)
   f = FP('f', Float32())
   s.add(fpAdd(RNE(), f, 1.0) == 3.0)

Differences from z3py are deliberate and documented in the package: ``==``
builds a term on every sort (``fpEQ`` is IEEE equality), ``bool(term)``
raises unless the term is a ground Boolean value, bit-vector ``<`` and ``>>``
are signed and arithmetic, ``/`` on bit-vectors raises (use ``UDiv``/``SDiv``),
and literals are strict (``BitVecVal(256, 8)`` raises; ``wrap=True`` wraps).
Options are keyword arguments with ``-`` and ``.`` spelled ``_``:
``Solver(max_time='2s', bb_div_v3=False)``.

The package installs with STP when it is built with ``ENABLE_PYTHON_API``
(the default when the interpreter can import Cython), or on its own, once per
interpreter, against an STP that is already installed:
``python3 -m pip install ./bindings/python`` compiles its extension there.
``bindings/python/README.md`` says how that finds the installation.

Running an input as ``stp`` does
--------------------------------

``Solver::parse`` and ``parse_smt2`` take a ``ParseMode``. ``DECLARE_AND_ASSERT``,
the default, adds an input's declarations and assertions to the solver and
decides nothing: the solver's own ``check_sat`` answers its question.
``EXECUTE`` runs the input as the ``stp`` binary does: an SMT-LIB 2 script's
commands answer as they are read, and a CVC or SMT-LIB 1 query is decided and
answered in that language's words. ``PARSE_ONLY`` reads it as ``--parse-only``
does. An input can also come from a ``std::istream``, read as its data
arrives, so a script driven over a pipe is answered command by command (in C
a ``stp_text_source`` callback, in Python ``Solver.from_stream``).

STP writes nothing to the process's streams. The answers, and what the
printing options print, go to the solver's output sink, where an empty chunk
asks for a flush; statistics, warnings and a fatal error's report go to its
diagnostic sink; without a sink the text is dropped. The one exception is a
SAT backend's own report, which ``print-functionstat`` switches on: CaDiCaL
and MiniSat print theirs to standard output themselves (CryptoMiniSat's
reaches the output sink). Three more hooks complete
what a command line needs: the CNF sink receives every CNF a check hands to the
SAT solver, with whether it is the whole query, partial (array read refinement
adds its axioms as the search asks for them) or an over-approximation (the
bit-vector abstractions); the fatal error handler hears of an engine fatal
error before anything unwinds, and may end the process; and
``input_to_string`` prints the last CVC or SMT-LIB 1 input back in the forms of
the ``--print-back`` options. The option ``end-after-cnf`` ends a run at its
first CNF, as ``--exit-after-CNF`` does. ``tools/stp/run.cpp``, the binary's
own use of these calls, is a complete example.

.. code-block:: python

   s = Solver()
   s.set_output_sink(sys.stdout.write)
   s.from_string("x : BITVECTOR(8); QUERY(x = x);", format="cvc", mode="execute")   # Valid.

.. _api-compat:

Compatibility with 2.x
----------------------

``libstp2`` implements ``c_interface.h`` over ``stp.h``, and is the only
library that provides it: KLEE and other 2.x clients link it unchanged
(``-lstp2`` instead of ``-lstp``; with CMake, the target ``stp2``, which the
package's ``STP_C_INTERFACE_LIBRARY``, ``STP_SHARED_LIBRARY`` and
``STP_STATIC_LIBRARY`` variables name). The header-only ``fp.hpp`` and
``uf.hpp`` over ``c_interface.h`` come with it. It reproduces the
2.x ownership modes, the error handler and the model-lifetime rules, with three
documented exceptions: reading a counterexample after a VALID answer returns
``NULL`` with a diagnostic instead of an invented value, an unmatched
``vc_pop`` is an error instead of deleting the base assertions, and a Real
constant or term beyond the exact-arithmetic budget is a fatal refusal, as any
constructor's is, where 2.x returned ``NULL``.
``lib/Compat2/NOTES.md`` records how each 2.x function, option letter and
``ifaceflag_t`` ordinal maps onto the 3.x API.

Limits of the alpha
-------------------

-  CryptoMiniSat is interrupted between its solver calls only.
-  ``fp.to_real`` takes formats whose exponent has at most 16 bits (the exact
   arithmetic's number limits), and a Real converts to a float only when it
   and the rounding mode are both values.
-  The float literal constructors (``mk_fp`` from a ``double`` or from text)
   need an exponent of at least 3 bits; ``mk_fp_from_bits`` builds a value of
   any format.
-  Arrays hold bit-vectors, floats, rounding modes and values of declared
   sorts, not Booleans.
-  ``unsat_assumptions`` after a batch check reports every assumption; the
   failed subset comes from a check the incremental driver ran.
-  ``stop-after-cnf`` stops the batch pipeline only: once pushes have made the
   session incremental, a check the incremental driver runs is answered.
-  Under ``simplify = false`` a few kinds still come back lowered, having no
   engine node of their own: ``BV_NAND``, ``BV_NOR`` and ``BV_XNOR`` as
   ``BV_NOT`` over the operation, ``BV_REPEAT`` and the rotations as
   concatenations, ``BV_COMP``, ``BV_REDAND`` and ``BV_REDOR`` as an ``ITE``
   over an equality, and ``DISTINCT`` over floats, Reals or arrays as the
   negation of an equality or a conjunction of them, among others.
-  A script run with ``ParseMode::EXECUTE`` answers its ``(check-sat)``
   inside the frontend, where the answer is printed; ``model()`` and
   ``unsat_assumptions()`` do not see it. In either mode a script's
   ``(check-sat)`` leaves each assertion level as one conjunction in
   ``assertions()``.
-  A function a script declares belongs to the manager, as a declared
   constant does: it survives an API ``pop()`` of the level it was declared
   in, and a later script over the same manager uses the name rather than
   declaring it again (a second declaration is a ``PARSE`` error, as SMT-LIB
   has it; ``declare`` is the idempotent door). A ``define-fun`` name lasts
   only for the script that defines it: ``symbol()``, a later script and
   ``parse_term`` do not see it.
-  A value of a declared sort prints as ``S!k``, which the parser does not
   read back.
-  A constant array indexed by a declared sort: a refutation that counts the
   sort's elements by its carrier (two constant arrays with different
   defaults, one reaching the other through writes) is answered unknown
   (``INCOMPLETE``), since a model may give the sort just the elements the
   writes name.
-  A function over Reals is modelled from the applications the check saw; one
   it never saw completes to the codomain's default. A Real argument with a
   bit-vector result under a comparison is refused at assertion.
-  An option's exclusions are checked when a solver is made, whenever both
   entries are set, whatever their values; ``set_args`` accepts ``--no-name``
   for every Boolean option.

``capabilities()`` reports the ones that depend on the build or the sort:
``interrupt.cryptominisat``, ``array.element-sorts`` and
``kind.FP_TO_FP_FROM_REAL``.

Several solvers, several threads
--------------------------------

Any number of solvers may be live over one manager, each with its own
assertion stack, options, models and statistics; switching between them replays the
assertion stack, which is the one cost. A manager and everything created from
it may be used from any thread, one call at a time: the caller serialises, and
``interrupt()`` is the one call that may overlap a running check.
