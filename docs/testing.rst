Introduction
============

STP currently supports the following types of tests

-  Tests that use query files (e.g. ``smt2`` files) to drive the ``stp``
   binary and check the tool's output. These are driven using the
   `lit <https://pypi.org/project/lit/>`__ and
   `OutputCheck <https://github.com/stp/OutputCheck>`__ tools. We refer
   to these as query file tests. They live in ``tests/query-files``.
-  Tests that call STP's API and check the results with the
   `GoogleTest <https://google.github.io/googletest/>`__ framework.
   Those under ``tests/unit-tests`` exercise STP's internals; those
   under ``tests/api`` exercise the public C, C++ and Python APIs.

Both kinds are registered with CTest, so ``ctest`` (or ``make test``)
runs everything.

Getting started
===============

We depend on a few external tools for testing. You need python3, and you
need GoogleTest and OutputCheck, which are downloaded into ``deps/`` by
the setup scripts (they used to be git submodules, they are not any
more):

::

    $ cd /path/to/stp
    $ ./scripts/deps/setup-gtest.sh
    $ ./scripts/deps/setup-outputcheck.sh

You also need the lit tool, which is available from
`PyPI <https://pypi.org/project/lit/>`__:

::

    $ pip install lit

Installing lit without root access
----------------------------------

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
-------------

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
   forced off when ``STATICCOMPILE`` is on.
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
-  ``USE_VALGRIND`` - Checks that Valgrind is in your ``PATH`` so that
   lit-driven GoogleTest suites can run under it.

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
``SimplifyFormula_TestTests-gtest``.

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

.. _query-file-tests-1:

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

.. _query-file-tests-2:

Query file tests
~~~~~~~~~~~~~~~~

You should take a look at the existing tests and at the
`lit <https://llvm.org/docs/CommandGuide/lit.html>`__, `LLVM
testing <https://llvm.org/docs/TestingGuide.html#writing-new-regression-tests>`__
and
`OutputCheck <https://github.com/stp/OutputCheck/blob/master/README.md>`__
documentation.

.. _unit-tests-1:

Unit tests
~~~~~~~~~~

You should take a look at some existing tests and read the `GoogleTest
documentation <https://google.github.io/googletest/>`__. A new test is
added by dropping a source file next to them and adding an
``AddSTPGTest(MyNew_Test.cpp)`` line to the ``CMakeLists.txt`` in that
directory; it is compiled, linked against ``libstp`` and GoogleTest, and
registered with CTest for you.
