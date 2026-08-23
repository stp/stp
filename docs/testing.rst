Testing
=======

Introduction
------------

STP currently supports the following types of tests

-  Tests that use query files (e.g. ``smt2`` files) to drive the ``stp``
   binary and check the tool's output. These are driven using the
   `lit <https://pypi.org/project/lit/>`__ and
   `OutputCheck <https://github.com/stp/OutputCheck>`__ tools. We refer
   to these as query file tests. They live in ``tests/query-files``.
-  Tests that call STP's API. Those under ``tests/unit-tests`` exercise
   STP's internals and those under ``tests/api/C`` and ``tests/api/CPP``
   exercise the public C and C++ APIs, all using the
   `GoogleTest <https://google.github.io/googletest/>`__ framework. The
   Python API tests under ``tests/api/python`` are plain Python scripts
   registered directly with CTest.

Both kinds are registered with CTest, so ``ctest`` (or ``make test``)
runs everything.

Getting started
---------------

We depend on a few external tools for testing. You need python3, and you
need GoogleTest and OutputCheck. With ``-DENABLE_AUTO_DOWNLOAD=ON`` the
build fetches both itself, at pinned revisions, into the build tree.
Otherwise they are downloaded into ``deps/`` by
the setup scripts (they used to be git submodules, they are not any
more):

::

    $ cd /path/to/stp

You also need the lit tool, which is available from
`PyPI <https://pypi.org/project/lit/>`__:

::

    $ pip install lit

Installing lit without root access
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If you don't want to install lit system-wide you can put it in a virtual
environment:

::

    $ python3 -m venv venv
    $ . venv/bin/activate
    (venv) $ pip install lit

Note how the shell prompt changes when the ``venv/bin/activate`` script
is executed from your shell. This is a hint that you are now using the
python virtual environment named ``venv``.

If you do this you need to make sure CMake picks up the python executable
in your virtual environment and not the system python executable. If you
have never executed CMake previously then configuring from a shell where
the environment is activated is enough -- CMake will find that python.

If you have configured previously (e.g. because you built STP with
testing disabled) then, from a shell with the environment activated, run
``make edit_cache`` in the build directory (``ninja edit_cache`` for
ninja) and either

-  Delete the ``PYTHON_EXECUTABLE`` cache variable and then configure. If
   all goes well you will see ``PYTHON_EXECUTABLE`` reappear, set to the
   full path of your virtual environment python. Once you have
   configured successfully you should regenerate the build system (i.e.
   press the generate button).

OR

-  Set the ``PYTHON_EXECUTABLE`` cache variable manually to the path of
   your virtual environment python and then configure and generate.

The same applies to ``LIT_TOOL``, which CMake sets to the first ``lit``
it finds in ``PATH``.

CMake options
~~~~~~~~~~~~~

There are various CMake options that allow control over testing. You can
easily configure these by…

-  When configuring for the first time use the ``cmake-gui`` or
   ``ccmake`` tool.
-  If you've already configured/built previously by running
   ``make edit_cache`` or ``ninja edit_cache`` in the build directory
   (this assumes you used the ``cmake-gui`` or ``ccmake`` tool when you
   first built).

At the time of writing the following options are available

-  ``ENABLE_TESTING`` - If enabled other testing options will be
   available. Note that testing needs a shared library build, so it is
   forced off when ``STATICCOMPILE`` is on, and it is forced off again
   when no Python 3 interpreter was found.
-  ``LIT_TOOL`` - Path to the ``lit`` executable (you shouldn't need to
   modify this normally)
-  ``LIT_ARGS`` - Arguments passed to ``lit`` when CTest invokes it,
   ``-s`` by default. Set it to e.g. ``-v`` to see the output of failing
   tests.
-  ``PYTHON_EXECUTABLE`` - Path to the python executable to use for
   testing programs. If you used a virtual environment to install
   ``lit`` you should ensure that this CMake variable is set to the
   virtual environment's python executable. This will happen
   automatically if you activated the environment before configuring.
-  ``TEST_QUERY_FILES`` - If enabled the query file tests under
   ``tests/query-files`` will become available for testing.
-  ``TEST_UNITS`` - If enabled the unit tests under ``tests/unit-tests``
   will become available for building/testing.
-  ``TEST_APIS`` - If enabled the tests under ``tests/api`` will become
   available.
-  ``TEST_C_API`` - If enabled the C API unit tests will be available
   for building/testing.
-  ``USE_VALGRIND`` - If enabled, every GoogleTest executable is run under
   valgrind's memcheck rather than directly, and memory errors fail the
   test. See :ref:`valgrind` below.
-  ``VALGRIND_ARGS`` - The flags CTest passes to valgrind. See
   :ref:`valgrind`.
-  ``VALGRIND_TEST_TIMEOUT`` - Per-test CTest timeout in seconds when
   ``USE_VALGRIND`` is on, three hours by default. The default timeout is
   not enough for the exhaustive tests once valgrind's slowdown is applied.

Running tests
-------------

To run all tests, from the build directory run

::

    $ make test

which is CTest's own target, so ``ctest`` does the same thing and takes
the more useful flags:

::

    $ ctest -j8              # run the suites in parallel
    $ ctest -N               # list the tests without running them
    $ ctest --output-on-failure
    $ ctest -R Rewriting     # run only tests whose name matches

The query file tests appear as a single CTest test named
``query-files``, which runs the whole lit suite. Each GoogleTest source
file becomes its own executable and its own CTest test, named after the
source file with ``Tests-gtest`` appended -- so
``tests/unit-tests/SimplifyFormula_Test.cpp`` is run by the CTest test
``SimplifyFormula_TestTests-gtest``. The tests that are not GoogleTest
are named individually: ``python-interface-tests``,
``python-allocator-tests``, ``test_fpbackend`` and ``test_fprewrites``.

.. _valgrind:

Running the tests under valgrind
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Configure with ``USE_VALGRIND`` and every GoogleTest executable is run
through valgrind's memcheck rather than being run directly, so ``ctest``
covers them as usual. Valgrind has to be in your ``PATH`` or configuration
fails.

::

    $ cmake -DENABLE_TESTING=ON -DUSE_VALGRIND=ON ..
    $ make
    $ ctest -j8

The flags come from ``VALGRIND_ARGS``, which defaults to
``--error-exitcode=1 --leak-check=full --errors-for-leak-kinds=none
--track-origins=yes``. Memory errors -- invalid accesses, uninitialised
values -- therefore fail a test, while leaks are reported in the output
without failing it. That split is deliberate: the tests under
``tests/api/C`` build ``Expr`` handles through the C API and mostly never
call ``vc_DeleteExpr``, so about thirty of them leak a few bytes each by
construction, and two of the unit tests drop what
``NodeDomainAnalysis::harmonise`` and ``FixedBits::GetMinBVConst`` hand
back. To make leaks fail as well, override the list -- remembering that
CMake lists are semicolon separated:

::

    $ cmake -DVALGRIND_ARGS="--error-exitcode=1;--leak-check=full;--errors-for-leak-kinds=definite" ..

Expect the suite to take well over an order of magnitude longer: 243
seconds versus 8 seconds at ``-j6`` on the machine this was measured on.
That is why the per-test CTest timeout is raised to
``VALGRIND_TEST_TIMEOUT`` (three hours by default) -- the exhaustive tests
do not fit in CTest's usual allowance once valgrind is in the way.

The query file tests are deliberately left out of this. They drive the
``stp`` binary, which links mimalloc by default, and mimalloc takes its
memory from ``mmap`` rather than ``malloc``, so memcheck cannot see the
individual allocations. Configure with ``-DSTP_ALLOCATOR=system`` if you
want to run the binary itself under valgrind, and use lit's own ``--vg``
flag for that.

.. _ubsan:

Running the tests under UndefinedBehaviorSanitizer
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Undefined behaviour does not announce itself. A build that executes it
answers exactly like a build that does not, right up until an optimiser or a
target decides otherwise, so it has to be looked for on purpose. Clang's
UndefinedBehaviorSanitizer compiles in the checks the language leaves to the
implementation -- signed overflow, out-of-range shifts, misaligned accesses --
and reports them as they happen.

::

    $ rtdir=$(dirname "$(clang -print-file-name=libclang_rt.ubsan_standalone-x86_64.so)")
    $ cmake -S . -B build-ubsan -G Ninja \
        -DENABLE_TESTING=ON -DPYTHON_EXECUTABLE="$(which python3)" \
        -DSTP_ALLOCATOR=system \
        -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
        -DCMAKE_C_FLAGS="-fsanitize=undefined -fno-sanitize-recover=all -fno-omit-frame-pointer" \
        -DCMAKE_CXX_FLAGS="-fsanitize=undefined -fno-sanitize-recover=all -fno-omit-frame-pointer" \
        -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=undefined -shared-libsan -Wl,-rpath,$rtdir" \
        -DCMAKE_SHARED_LINKER_FLAGS="-fsanitize=undefined -shared-libsan -Wl,-rpath,$rtdir"
    $ cmake --build build-ubsan
    $ ctest --test-dir build-ubsan -j8

``CMAKE_C_FLAGS`` matters as much as the C++ one: ABC, the vendored library
that turns each query's AIG into CNF, is C, and is where the undefined
behaviour found so far has been. This is not what the ``SANITIZE``
configuration variable does -- that one sets C++ flags only, and turns on the
address and integer sanitizers as well.

``-fno-sanitize-recover=all`` makes a failing check abort rather than print
and carry on, which is what turns undefined behaviour into a failing test.
``UBSAN_OPTIONS=halt_on_error=1`` would do the same thing for a run that
remembers to set it -- lit does forward that variable to the query file tests
-- but compiling it in makes it a property of the binary, so it holds however
the binary is reached, including through the Python bindings. Leave the flag
off when you would rather collect every report from a run than stop at the
first, and set ``UBSAN_OPTIONS=print_stacktrace=1`` for a stack trace with
each one.

The rest is plumbing. ``-shared-libsan`` and the matching ``-rpath`` are what
let ``python-interface-tests`` work: the bindings dlopen ``libstp.so``, which
fails against clang's default static runtime with "undefined symbol:
``__ubsan_handle_type_mismatch_v1``". ``STP_ALLOCATOR=system`` keeps the
vendored mimalloc, which replaces ``malloc`` wholesale, out of the picture.

CI runs this configuration on every pull request, as the ``clang (ubsan)``
job in ``.github/workflows/ci.yml``.

Notes for Query file tests
--------------------------

The query file tests can also be driven by running ``lit`` yourself. The
lit configuration is generated into the build tree and named after the
build type, so pass that as the config prefix and run lit from the build
directory:

::

    $ cd /path/to/stp/build
    $ lit --config-prefix=Release tests/query-files

Use the ``CMAKE_BUILD_TYPE`` you configured with (``Debug``,
``RelWithDebInfo``, …) in place of ``Release``.

When using the ``lit`` tool it is possible to pass various handy
parameters.

::

    $ lit --config-prefix=Release --param=solver=/path/to/solver tests/query-files

This will change the solver from the STP you just built to a solver of
your choice.

::

    $ lit --config-prefix=Release --param=solver_params="-flag1 -flag2" tests/query-files

This will pass additional flags to the solver. There is also
``--param=outputcheck_params=...`` for passing extra flags to
OutputCheck.

Individual tests
----------------

Query file tests
~~~~~~~~~~~~~~~~

The lit tool gives you the ability to easily run a subset of tests: pass
it a subdirectory or an individual query file instead of the whole
suite.

::

    $ cd /path/to/stp/build
    $ lit -v --config-prefix=Release tests/query-files/misc-tests \
          tests/query-files/simplification-tests/alwaysTrue.smt2

Unit tests
~~~~~~~~~~

The unit tests are built as standalone executables so individual tests
can be executed by just running their executables, which live in the
build directory under the same path they have in the source tree --
``tests/unit-tests`` and ``tests/api/C``. Because they are GoogleTest
binaries they take the usual flags, e.g. ``--gtest_filter=...`` to run a
subset of the cases in one executable.

Writing tests
-------------

Query file tests
~~~~~~~~~~~~~~~~

You should take a look at the existing tests and at the
`lit <https://llvm.org/docs/CommandGuide/lit.html>`__, `LLVM
testing <https://llvm.org/docs/TestingGuide.html#writing-new-regression-tests>`__
and
`OutputCheck <https://github.com/stp/OutputCheck/blob/master/README.md>`__
documentation.

Unit tests
~~~~~~~~~~

You should take a look at some existing tests and read the `GoogleTest
documentation <https://google.github.io/googletest/>`__. A new test is
added by dropping a source file next to them and adding an
``AddSTPGTest(MyNew_Test.cpp)`` line to the ``CMakeLists.txt`` in that
directory; it is compiled, linked against ``libstp`` and GoogleTest, and
registered with CTest for you.
