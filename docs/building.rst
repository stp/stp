Building STP
============

The overview page has the recipe that works from a clean checkout. This
page is the detail behind it: what STP depends on, which SAT backend to
build against, and the configuration variables worth knowing.

STP is built with `CMake <https://cmake.org/>`__, version 3.18 or newer.
CMake is a meta build system that generates build files for other tools
such as make(1), Visual Studio and Xcode. The 3.18 floor comes from the
vendored mimalloc, which is the default allocator; on an older CMake,
configure with ``-DSTP_ALLOCATOR=system`` to skip it and use the C
library's malloc instead.

Dependencies
------------

STP relies on flex, bison and python3, plus at least one SAT backend.
Configuration fails if no backend is enabled.

On a Debian-like platform most of it comes from the package manager:

.. code-block:: bash

    sudo apt-get install git build-essential cmake bison flex python3

A python3 interpreter is needed at build time -- it generates the AST kind
tables -- and also for the Python interface and the test suite. git is needed
for the submodules, for the vendored-patch step that runs at configure time,
and to fetch LibBF.

The SAT backends bring their own dependencies, which are needed only if you
build that backend, and which the ``scripts/deps`` script for each one names:
CryptoMiniSat needs GMP (``libgmp-dev``), MiniSat needs zlib
(``zlib1g-dev``). Neither is used by STP itself.

Four dependencies are vendored as submodules and need nothing installed:
ABC, mimalloc, the command-line parser
`CLI11 <https://github.com/CLIUtils/CLI11>`__, and the header-only
floating-point library `SymFPU <https://github.com/martin-cs/symfpu>`__.
Run ``git submodule update --init`` after cloning; the build does not
configure without them.

One is fetched and built by a script rather than vendored:
`LibBF <https://bellard.org/libbf/>`__, which converts the real literals
in floating-point input -- ``((_ to_fp 8 24) RNE 1.5)``. It is required.
Run ``scripts/deps/setup-libbf.sh`` from the top of the source tree
before configuring: it clones `stp/libbf <https://github.com/stp/libbf>`__
at a pinned commit and builds ``libbf.a`` into ``deps/libbf``, where the
build looks by default. Point ``LIBBF_DIR`` at a copy built somewhere else
to skip the script -- an offline build wants that, since the script clones.

Upstream LibBF publishes release tarballs and no git repository, which is
what ``stp/libbf`` is for. It is laid out like STP's ABC fork: ``master``
holds the release tarballs verbatim, one commit each, and ``stp`` -- the
branch the pin names -- adds STP's MSVC portability changes on top. Moving
to a newer release means importing its tarball there and rebasing ``stp``
onto it, then moving the pin here.

SAT backends
------------

CryptoMiniSat is the default backend, and the one the install
instructions build. CMake finds it automatically when it is installed,
including into ``deps/install``, where ``scripts/deps/setup-cms.sh``
puts it:

.. code-block:: bash

    git clone https://github.com/msoos/cryptominisat
    cd cryptominisat
    mkdir build && cd build
    cmake ..
    cmake --build . -j$(nproc)
    sudo cmake --install .
    command -v ldconfig && sudo ldconfig

``-DNOCRYPTOMINISAT=ON`` ignores an installed copy.

CaDiCaL is the alternative, and is worth trying on hard bitvector
problems. It is opt-in rather than auto-detected, and is consumed from a
build tree rather than an installation, so ``CADICAL_DIR`` points at the
checkout:

.. code-block:: bash

    git clone https://github.com/arminbiere/cadical
    cd cadical
    git checkout rel-3.0.1
    ./configure -fPIC
    make

Then configure STP with ``-DUSE_CADICAL:BOOL=ON -DCADICAL_DIR:PATH=<path>``,
where ``<path>`` is the checkout containing ``src/cadical.hpp`` and
``build/libcadical.a``. ``-fPIC`` is required, because ``libcadical.a``
is linked into STP's shared library. These commands are pre-configured in
``scripts/deps/setup-cadical.sh``.

Enabling CaDiCaL makes it the default for that build, in place of
CryptoMiniSat; ``--cryptominisat`` (or ``--minisat``, in a
``-DUSE_MINISAT`` build) selects another backend at run time. With a
CaDiCaL 3.x build, ``--cadical-factor`` controls CaDiCaL's bounded
variable addition: ``on`` -- the default -- ``off``, or ``auto``, which
enables it only for problems with array operations. ``auto`` was the
default until bounded variable addition was measured on bitvector-only
problems and found to pay there too.

MiniSat is optional and off by default; enable it with
``-DUSE_MINISAT:BOOL=ON``, which also needs zlib. Your distribution's
minisat package works, or STP maintains an updated fork:

.. code-block:: bash

    git clone https://github.com/stp/minisat
    cd minisat
    mkdir build && cd build
    cmake ..
    cmake --build . -j$(nproc)
    sudo cmake --install .
    command -v ldconfig && sudo ldconfig

The MiniSat and CryptoMiniSat recipes above are pre-configured in
``scripts/deps/setup-minisat.sh`` and ``scripts/deps/setup-cms.sh``.
Those scripts install into ``deps/install``, which CMake searches without
any extra flags.

The Riss solver can be enabled with ``-DUSE_RISS``, which also needs
``-DRISS_DIR=<path>`` naming a Riss checkout that contains
``riss/core/Solver.h`` and ``build/lib/libriss-coprocessor.a``;
configuration fails without it. ``scripts/deps/setup-riss.sh`` builds one.

Building against non-installed libraries
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To build STP's dependencies without installing them, tell CMake where the
artefacts are:

-  ``-DMINISAT_INCLUDE_DIRS:PATH=<path>`` and
   ``-DMINISAT_LIBDIR:PATH=<path>`` -- the paths to
   ``minisat/core/Solver.h`` and to the ``minisat`` libraries
-  ``-Dcryptominisat5_DIR:PATH=<path>`` -- the path to
   ``cryptominisat5Config.cmake``

If the development libraries were not installed, ``MINISAT_LIBDIR`` can
be set to minisat's ``build`` directory, and ``cryptominisat5_DIR`` to
CryptoMiniSat's.

Floating-point support
----------------------

Floating-point support is always built, backed by the vendored SymFPU
submodule (``git submodule update --init lib/extlib-symfpu/symfpu`` if
you cloned without ``--recursive``). An external SymFPU clone can be used
instead, via ``-DSYMFPU_INCLUDE_DIRS=<directory containing the clone>``.

STP solves the SMT-LIB floating-point theory and exposes floating-point
terms through the C, C++ (``stp/fp.hpp``) and Python APIs. Real literals
under ``to_fp`` -- ``((_ to_fp 8 24) RNE 0.1)`` -- are folded to their
exactly-rounded bits while parsing, in any format and under any of the
five rounding modes. One operation is format-bounded: ``fp.rem`` is
refused past roughly binary64-sized formats, because its circuit unrolls
one divide step per representable exponent difference, which for
Float128 would be some 33000 steps deep.

Configuration variables
-----------------------

These apply to all generators:

-  ``CMAKE_BUILD_TYPE`` -- the build type, e.g. Release
-  ``CMAKE_INSTALL_PREFIX`` -- the prefix to install under, e.g.
   ``/usr/local``
-  ``ENABLE_ASSERTIONS`` -- build with assertions
-  ``ENABLE_TESTING`` -- enable running the tests
-  ``ENABLE_PYTHON_INTERFACE`` -- build the Python interface (Python 3
   only)
-  ``PYTHON_EXECUTABLE`` -- which Python 3 to use, when more than one is
   installed
-  ``SANITIZE`` -- use Clang's sanitization checks. It sets C++ flags only,
   and turns on the address and integer sanitizers alongside the undefined
   one; for the undefined-behaviour build CI runs, which also covers the
   vendored C, see :ref:`ubsan`
-  ``STATICCOMPILE`` -- build static libraries and binaries instead of
   dynamic
-  ``BUILD_SHARED_LIBS`` -- build ``libstp`` as a shared library
   (default ON; forced OFF by ``STATICCOMPILE``)
-  ``NOCRYPTOMINISAT`` -- do not use CryptoMiniSat, even if it is
   installed
-  ``USE_CADICAL`` and ``CADICAL_DIR`` -- build against a CaDiCaL
   checkout
-  ``USE_MINISAT`` -- build the MiniSat backend
-  ``USE_RISS`` -- build the Riss backend
-  ``TUNE_NATIVE`` -- build with ``-mtune=native``
-  ``WERROR`` -- treat compiler warnings as errors
-  ``SYMFPU_INCLUDE_DIRS`` -- build against an external SymFPU clone
   rather than the vendored submodule (point it at the directory
   *containing* the clone)
-  ``LIBBF_DIR`` -- where to find the built LibBF (defaults to
   ``deps/libbf``, where ``scripts/deps/setup-libbf.sh`` puts it)
-  ``STP_ALLOCATOR`` -- which memory allocator the ``stp`` binary uses.
   STP is allocation-heavy and the C library allocator is a significant
   bottleneck, so this defaults to ``mimalloc``, which is vendored and
   built as part of STP. Set it to ``tcmalloc`` to link a system
   gperftools instead, or to ``system`` for plain ``malloc`` -- roughly
   14% slower, but the lowest peak memory. Only the executables link the
   allocator; ``libstp`` leaves the choice to whatever application embeds
   it.

There are three ways to set them, in decreasing order of friendliness:
run ``cmake-gui`` on the source root instead of ``cmake``, which also
lets you pick the generator; run ``ccmake``, which is the same idea in an
ncurses terminal interface; or pass ``-D<VARIABLE>=<VALUE>`` to ``cmake``,
which is best kept for scripts. An already-configured build can be
changed with ``make edit_cache``, which reconfigures and regenerates.

Building a static library and binary
------------------------------------

.. code-block:: bash

    mkdir build && cd build
    cmake -DSTATICCOMPILE=ON ..
    cmake --build . -j$(nproc)
    sudo cmake --install .
    command -v ldconfig && sudo ldconfig

Installing
----------

``make install`` installs, ``make uninstall`` removes. The root of the
installation is ``CMAKE_INSTALL_PREFIX``, set at configure time or
changed later through ``make edit_cache``.

Building on Windows and Visual Studio
-------------------------------------

Install `CMake <https://cmake.org/download/>`__ and follow the steps that
one of the two Windows jobs in
`.github/workflows/ci.yml <https://github.com/stp/stp/blob/master/.github/workflows/ci.yml>`__
runs. Both install flex and bison, build LibBF, and configure with
``-DNOCRYPTOMINISAT=ON``, CryptoMiniSat not being buildable there.

``windows (cadical, MinGW)`` is the one to follow for a solver to use: it
builds CaDiCaL under MinGW/UCRT64 and links a fully static ``stp.exe``
against it. ``windows (minisat, MSVC)`` builds with Visual Studio instead,
where MiniSat is the only backend that compiles.

Testing
-------

See :doc:`testing`.
