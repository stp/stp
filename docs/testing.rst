Introduction
============

STP currently supports the following types of tests

-  Tests that use query files (e.g. ``smt2`` files)
   to drive the ``stp`` binary and check the tool’s output. These are
   driven using the `lit <https://pypi.python.org/pypi/lit>`__ and
   `OutputCheck <https://github.com/stp/OutputCheck>`__ tools. We refer
   to these as query file tests.
-  Tests that use STP’s API and are checked using the GoogleTest
   framework and driven using lit. We refer to these as unit tests.

Getting started
===============

We depend on various external tools to do testing. Firstly you should
install python. Secondly you should initialise STP’s git submodules to
get the GoogleTest and OutputCheck code.

::

    $ cd /path/stp/src
    $ git submodule init
    $ git submodule update

Now you need to install the lit tool which is available from
`PyPi <https://pypi.python.org/pypi>`__. An easy way to install the tool
is using the ``pip`` tool.

::

    $ pip install lit

Note that for Ubuntu 14.04 you need install the ``python-stdeb``
package, fix the URL in ``/usr/bin/pypi-install`` to
``https://pypi.python.org/pypi`` and then execute
``sudo pypi-install lit``.

Installing lit without root access
----------------------------------

If you don’t have root access to your machine you can use the
`virtualenv <http://www.virtualenv.org/en/latest/>`__ tool to install
lit in a local python environment.

::

    $ cd /path/to/put/your/virtual_environment
    $ virtualenv venv
    Using base prefix '/usr'
    New python executable in venv/bin/python3
    Also creating executable in venv/bin/python
    Installing setuptools, pip...done.
    $ . venv/bin/activate
    (venv) $ pip install lit
    Downloading/unpacking lit
      Downloading lit-0.3.0.tar.gz (45kB): 45kB downloaded
    ...                                                                                                                                  
    Successfully installed lit                                                                                                                                                                                         
    Cleaning up...
    (venv) $

Note how the shell prompt changes when the ``venv/bin/activate`` script
is executed from your shell. This is a hint that you are now using the
python virtual environment named ``venv``

Note if you do this you need to make sure CMake is aware that you want
to use the python executable in your virtual environment and not the
system python executable.

If you have never executed CMake previously then if you run it from a
shell where you have activated your virtual environemt (i.e.
``venv/bin/activate``) then when CMake is configuring it will detect
your virtual environment python executable.

If you have executed CMake previously (e.g. because you have already
built STP perhaps with testing disabled) then in a shell with your
python virtual environment enabled you should run ``make edit_cache``
from the STP build directory root (``ninja edit_cache`` for ninja) and
then do one of the following

-  Delete the ``PYTHON_EXECUTABLE`` cache variable and then configure.
   If all goes well you will see the ``PYTHON_EXECUTABLE`` reappear set
   to the full path to your virtual environment python executable. Once
   you have configured successfully you should regenerate the build
   system (i.e. press the generate button).

OR

-  Set the ``PYTHON_EXECUTABLE`` cache variable manually to the path to
   your virtual environment python executable and then configure and
   generate.

CMake options
-------------

There are various CMake options that allow control over testing. You can
easily configure these by…

-  When configuring for the first time use the ``cmake-gui`` or
   ``ccmake`` tool.
-  If you’ve already configured/built previously by running
   ``make edit_cache`` or ``ninja edit_cache`` in the build directory
   (this assumes you used the ``cmake-gui`` or ``ccmake`` tool when you
   first built).

At the time of writing the following options are available

-  ``ENABLE_TESTING`` - If enabled other testing options will be
   available
-  ``LIT_TOOL`` - Path to the ``lit`` executable (you shouldn’t need to
   modify this normally)
-  ``PYTHON_EXECUTABLE`` - Path to the python executable to use for
   testing programs. If you used ``virtualenv`` to install ``lit`` you
   should ensure that this CMake variable is set to the path to the
   ``virtualenv`` python executable. This will happen automatically if
   you used the virtualenv ``activate`` script before configuring.
-  ``TEST_APIS`` - If enabled the tests available under ``tests/api``
   will become available.
-  ``TEST_C_API`` - If enabled the C API unit tests will be available
   for building/testing.
-  ``TEST_QUERY_FILES`` - If enabled the query file tests will be
   available for testing.
-  ``USE_VALGRIND`` - If enabled Valgrind will be used for unit tests.

Running tests
-------------

To attempt to run all tests from the build directory (assuming you are
using the Makefile generated build system) run

::

    $ make check

Note if any tests fail other test suites will not execute (unless you
pass the ``-i`` flag to make).

Notes for Query file tests
--------------------------

When using the ``lit`` tool to run query file tests it is possible to
pass various handy parameters.

::

    $ lit --param=solver=/path/to/solver .

This will change the solver from STP to a solver of your choice

::

    $ lit --param=solver_params="-flag1 -flag2 -flag3" .

This will pass additional flags to the solver ## Individual test suites

Query file tests
~~~~~~~~~~~~~~~~

To run the query file tests run

::

    $ make query-file-tests

to run directly using ``lit`` run

::

    $ cd /path/to/stp/build/
    $ lit tests/query-files

C API tests
~~~~~~~~~~~

To run and build the C-api tests run

::

    $ make C-api-tests

Individual tests
----------------

.. _query-file-tests-1:

Query file tests
~~~~~~~~~~~~~~~~

When running the query file tests the lit tool gives you the ability to
easily run a subset of tests. For example say you are in the
``tests/query-files`` directory. You can do the following

::

    $ lit -v misc-tests/ unit_test/alwaysTrue.smt2

This will run all tests under the ``tests/misc-tests`` folder and run
the ``unit_test/alwaysTrue.smt2`` test.

Unit tests
~~~~~~~~~~

The unit tests are built as standalone executables so individual tests
can be executed by just running their executables.

For example for the C API tests the built tests can be found in
``tests/api/C`` in the build directory.

Writing tests
-------------

.. _query-file-tests-2:

Query file tests
----------------

You should take a look the existing tests and at the
`lit <http://llvm.org/docs/CommandGuide/lit.html>`__, `LLVM
testing <http://llvm.org/docs/TestingGuide.html#writing-new-regression-tests>`__
and
`OutputCheck <https://github.com/stp/OutputCheck/blob/master/README.md>`__
documentation.

.. _unit-tests-1:

Unit tests
----------

You should take a look at some existing testsand read the `GoogleTest
documentation <https://code.google.com/p/googletest/wiki/Documentation>`__.
