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
  check, ``interrupt()`` (safe from any thread), parsing of SMT-LIB 2 input,
  printing, statistics.

``Model``
  A detached snapshot: it survives every later assertion, push or pop, and it
  evaluates any term of its manager, including terms built after the check.
  Symbols the solver never assigned are completed with their sort's default;
  ``try_value`` refuses to complete instead. An array's value is a term, the
  constant array of its default under a store per cell; a function has no
  value term, and ``function_value`` reads its table.

``Options``
  The whole option registry of the ``stp`` binary, settable by name with the
  text form the command line uses, or through typed setters. Every entry has a
  tier (stable, expert, experimental, diagnostic) and a settable window
  (anytime, before the first check, at construction); a write outside the
  window is a recoverable error, never silent. The binary registers its own
  command line from the same registry, so an option has one spelling and one
  meaning whether it arrives as ``--name`` or through ``Options::set``, and
  the binary's only additions are its frontend switches (input format,
  printing, ``--parse-only``, ``--interactive``). Three things differ on the
  command line, as ``stp --help`` shows: ``produce-models`` and
  ``lra-verify-canonical`` default to off there, a duration such as
  ``--max-time`` is a bare number of seconds, and ``--logic`` sets only the
  logic's switches for the uninterpreted functions and extensional arrays.

Errors are exceptions in C++ and Python and a per-manager error record in C.
Every precondition is checked in every build type; a recoverable error leaves
every object as it was. The library never calls ``exit()`` or ``abort()``: a
script the frontend refuses (a sort error, a wrong arity, a constant that
does not fit its width) is a ``PARSE`` error with the solver as it was, and an
engine failure inside any call is ``INTERNAL`` and poisons the manager, after
which every call on it, its solvers, models and terms is refused with
``STATE`` naming the failure.

Names supplied to ``declare``, ``declare_sort`` and ``bind_symbol``, and
prefixes supplied to ``mk_fresh`` and ``mk_fresh_sort``, must be representable
as SMT-LIB quoted symbols. Spaces, non-ASCII bytes (including UTF-8), tabs,
newlines and carriage returns are allowed. NUL, ``|``, backslash, DEL and
other ASCII control characters are rejected, as are names or prefixes
beginning with ``@`` or ``.`` (reserved for solver use). Names must be
nonempty; fresh-name prefixes may be empty. A rejected name gives
``INVALID_ARGUMENT`` before any declaration or binding is recorded. Python
raises ``ArgumentError``, except for its existing NUL check, which raises
``ValueError``. C strings end at their first NUL; C++ counted strings are
checked in full. Theory-predefined names such as ``true`` and ``bvadd``
cannot be declared or bound, and predefined sort names such as ``Bool``
cannot be declared, because quoting does not distinguish them.

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
   s.add(a == store(tm.declare("b", arr), i, tm.mk_bv(8, 42)));  // extensional
   s.add(a != tm.mk_const_array(arr, tm.mk_bv(8, 0)));          // ((as const ...) #x00)

   Sort f32 = tm.mk_fp32_sort();
   Term fx = tm.declare("fx", f32);
   s.add(fp_add(RoundingMode::RNE, fx, 1.0) == tm.mk_fp(f32, RoundingMode::RNE, 3.0));

   Term f = tm.declare("f", tm.mk_fun_sort({bv32}, bv32));
   s.add(f(x) == f(y));

   Term r = tm.declare("r", tm.mk_real_sort());
   s.add(real_lt(r + 1, tm.mk_real("3/2")));

   if (s.check_sat().is_sat())
   {
     Model m = s.model();
     FloatValue v = m.fp_value(fx);           // sign, exponent, significand, class
     FunctionValue fv = m.function_value(f);  // entries and a default
     RationalValue q = m.real_value(r);       // numerator and denominator
   }

Options are set at construction or on the live solver:

.. code-block:: cpp

   Options o;
   o.set("max-time", "2s");           // the text form: a duration needs its unit here
   o.set_str("sat-backend", "cadical");
   o.set_args({"--fp-abstraction", "--bb.div-v3=false"});
   Solver s(tm, o);
   s.options().set_bool("check-sanity", true);   // anytime
   Result r = s.check_sat({assumption}, CheckBudget{std::chrono::milliseconds(500), std::nullopt});
   if (r.is_unknown()) std::cout << r.reason_message();

A duration option's ``none`` (no limit; ``max-time``'s default) is ``-1ms``
to ``get_duration`` and ``set_duration``, and ``STP_DURATION_NONE`` to the C
``*_duration_ms`` functions, so a value read back can be written back.

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

The package's own rules, documented in it: ``==`` builds a term on every
sort (``fpEQ`` is IEEE equality); ``bool(term)`` raises unless the term is a
ground Boolean value, so ``x in [y, x]``, ``list.index`` and ``list.remove``
over terms raise too; bit-vector ``<`` and ``>>`` are signed and arithmetic
(``ULT``, ``LShR`` and the rest are the unsigned and logical forms), and ``/``
on bit-vectors raises (use ``UDiv``/``SDiv``), except inside the ``@stp``
decorator, which keeps STP 2.x's unsigned meanings; literals are strict
(``BitVecVal(256, 8)`` raises; ``wrap=True`` wraps); ``Model.eval`` completes
by default (``model_completion=False`` leaves a symbol the model does not fix
in place); ``as_decimal(k)`` always gives ``k`` digits
(``Q(1, 2).as_decimal(3)`` is ``"0.500"``); and ``fpToFP`` takes a rounding
mode first, the bits of a bit-vector read as a float being ``fpBVToFP``.
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
``EXECUTE`` runs the input as the ``stp`` binary does: a script's commands
answer as they are read. ``PARSE_ONLY`` reads it as ``--parse-only`` does. An input can also come from a ``std::istream``, read as its data
arrives, so a script driven over a pipe is answered command by command (in C
a ``stp_text_source`` callback, in Python ``Solver.from_stream``).

A script's ``reset`` or ``reset-assertions`` can discard its declarations,
but the term manager retains declarations from the API and earlier parses,
and existing handles remain valid. Reusing a retained name for a different
symbol or sort is a recoverable ``PARSE`` error; the solver's assertion stack
is restored. An ordinary symbol redeclared at the same sort keeps its
identity. A ``declare-sort`` always introduces a new sort identity, so it
cannot reuse a retained sort name even after reset. Use the existing sort
without redeclaring it in a subsequent parse, or use a fresh term manager
and solver when a script needs a new namespace. Declarations created and
discarded within one script still follow SMT-LIB scope and reset rules.

STP writes nothing to the process's streams. The answers, and what the
printing options print, go to the solver's output sink, where an empty chunk
asks for a flush; statistics, warnings and a fatal error's report go to its
diagnostic sink; without a sink the text is dropped. The one exception is a
SAT backend's own report, which ``print-functionstat`` switches on: CaDiCaL
and MiniSat print theirs to standard output themselves (CryptoMiniSat's
reaches the output sink). Two more hooks complete
what a command line needs: the CNF sink receives every CNF a check hands to the
SAT solver, with whether it is the whole query, partial (array read refinement
adds its axioms as the search asks for them) or an over-approximation (the
bit-vector abstractions); and the fatal error handler hears of an engine fatal
error before anything unwinds, and may end the process. The option
``end-after-cnf`` ends a run at its
first CNF, as ``--exit-after-CNF`` does. ``tools/stp/run.cpp``, the binary's
own use of these calls, is a complete example.

.. code-block:: python

   s = Solver()
   s.set_output_sink(sys.stdout.write)
   s.from_string("(declare-fun x () (_ BitVec 8))\n(assert (distinct x x))\n(check-sat)\n",
                 mode="execute")   # unsat

.. _api-compat:

Compatibility with 2.x
----------------------

``libstp2`` implements ``c_interface.h`` over ``stp.h``, and is the only
library that provides it: KLEE and other 2.x clients link it unchanged
(``-lstp2`` instead of ``-lstp``; with CMake, the target ``stp2``, which the
package's ``STP_C_INTERFACE_LIBRARY``, ``STP_SHARED_LIBRARY`` and
``STP_STATIC_LIBRARY`` variables name). The header-only ``fp.hpp`` and
``uf.hpp`` over ``c_interface.h`` come with it. It reproduces the
2.x ownership modes, the error handler and the model-lifetime rules, with four
documented exceptions: reading a counterexample after a VALID answer returns
``NULL`` with a diagnostic instead of an invented value, an unmatched
``vc_pop`` is an error instead of deleting the base assertions, a Real
constant or term beyond the exact-arithmetic budget is a fatal refusal, as any
constructor's is, where 2.x returned ``NULL``, and a parsed text that declares
a name the checker already has at another type is refused, where 2.x made a
second symbol of that name.
``lib/Compat2/NOTES.md`` records how each 2.x function, option letter and
``ifaceflag_t`` ordinal maps onto the 3.x API.

Limits of the alpha
-------------------

-  CryptoMiniSat is interrupted between its solver calls only, and so is
   MiniSat when the MiniSat it was built with lacks the terminator hook of
   stp/minisat (``capabilities()`` says which, under ``interrupt.minisat``).
-  The model's evaluator, ``simplify``, ``substitute`` and ``str()`` take a
   term of any depth. The engine's printers -- ``to_string`` with let-sharing,
   the DOT and GDL forms, and ``Solver::to_smt2`` and ``to_string`` --
   recurse once per level of a term, as 2.x's did, and a term some ten
   thousand levels deep can overflow the stack there.
-  ``fp.to_real`` takes formats whose exponent has at most 16 bits (the exact
   arithmetic's number limits), and a Real converts to a float only when it
   and the rounding mode are both values. Relating two conversions costs about
   four times more per exponent bit: well under a second at binary64, a minute
   or more at binary128; at 16 bits it exceeds the number limits, and the check
   answers unknown (``INCOMPLETE``). At 16 bits a check over a single
   conversion can exceed them too, depending on the SAT backend.
-  The float literal constructors (``mk_fp`` from a ``double`` or from text)
   and SMT-LIB real-literal conversions need an exponent field of at least
   3 bits. Wider fields, including those larger than a machine word, accept
   ordinary values with the requested rounding mode. For fields wider than
   LibBF supports directly (29 bits with 32-bit limbs, 61 with 64-bit limbs),
   a nonzero result's unbiased exponent must fit its working normal range:
   ``2 - 2^28`` through ``2^28 - 1`` with 32-bit limbs, or
   ``2 - 2^60`` through ``2^60 - 1`` with 64-bit limbs. Magnitudes outside
   that range are refused; they are not rounded to the narrower working
   format's zero, infinity or largest finite value. ``mk_fp_from_bits``
   builds a value of any format without these conversion limits.
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
-  A constant array's default must be a value, a term with no symbol in it:
   ``mk_const_array`` over a variable, or over a term that contains one, is
   ``UNSUPPORTED``, and so is a script's ``((as const S) v)`` (a ``PARSE``
   error). An array of a declared sort's values takes one a model gave.
-  A constant array indexed by a declared sort: a refutation that counts the
   sort's elements by its carrier (two constant arrays with different
   defaults, one reaching the other through writes) is answered unknown
   (``INCOMPLETE``), since a model may give the sort just the elements the
   writes name.
-  A function over Reals is modelled from the applications the check saw; one
   it never saw completes to the codomain's default. A Real argument with a
   bit-vector result under a comparison is refused at assertion.
-  A Real comparison belongs at the Boolean level: one that stays inside a
   bit-vector term -- the condition of a bit-vector ``ite``, ``bool_to_bv1``
   of it -- is refused at assertion (``UNSUPPORTED``) unless simplification
   brings it up (``bool_to_bv1(r == 1) == 1`` is ``r == 1``).
-  An option's exclusions are checked when a solver is made, whenever both
   entries are set, whatever their values; ``set_args`` accepts ``--no-name``
   for every Boolean option.

``capabilities()`` reports the ones that depend on the build or the sort:
``interrupt.cryptominisat``, ``interrupt.minisat`` (in a build with MiniSat),
``array.element-sorts`` and ``kind.FP_TO_FP_FROM_REAL``.

Several solvers, several threads
--------------------------------

Any number of solvers may be live over one manager, each with its own
assertion stack, options, models and statistics; switching between them replays the
assertion stack, which is the one cost. A manager and everything created from
it may be used from any thread, one call at a time: the caller serialises, and
``interrupt()`` is the one call that may overlap a running check.

Independent managers run concurrently, with one exception: the parsers keep
process-wide state, so every parse takes one lock for its whole length. A
check that an ``EXECUTE`` input runs, and a wait on the stream or text source
a parse reads, hold it too, and a parse on another manager waits for them.

A callback -- an output, diagnostic or CNF sink, the terminator, the
fatal-error handler, the stream a parse reads, C's error callback -- runs in
the middle of a call, and must not call the library: every call from one is
refused with ``STATE``, but ``interrupt()``, ``clear_interrupt()`` and
``interrupt_pending()``.
