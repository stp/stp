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
Nothing else has to be installed: with ``-DENABLE_AUTO_DOWNLOAD=ON`` the
build fetches every library it needs, and ``lit``, which drives the
tests, into a virtual environment of its own.
Configuration fails if no backend is enabled.

On a Debian-like platform most of it comes from the package manager:

.. code-block:: bash

    sudo apt-get install git build-essential cmake bison flex python3

A python3 interpreter is needed at build time -- it generates the AST kind
tables -- and also for the Python interface and the test suite. git is needed
to fetch the dependencies, which are cloned rather than downloaded as
archives where their revision is a commit rather than a release.

The SAT backends bring their own dependencies, which are needed only if you
build that backend, and which the ``scripts/deps`` script for each one names:
CryptoMiniSat needs GMP (``libgmp-dev``), MiniSat needs zlib
(``zlib1g-dev``). Neither is used by STP itself.

STP has no submodules. Everything it does not contain itself is fetched
at a pinned revision, and with ``-DENABLE_AUTO_DOWNLOAD=ON`` that needs
nothing installed beforehand.

Most are ExternalProjects: built at build time, installed into
``STP_DEP_DIR``, and so built once however many build directories are
pointed at the same one. ABC is among them, which matters because it is
920 C files -- but it also means every build sharing a dependency
directory shares one ABC, compiled with one set of flags. Its
optimisation level is whichever configuration built it first; its
*defines* are not left to chance, because STP's own sources include
ABC's headers and the two have to agree, so they are recorded in the
directory's stamp and a mismatch is reported.

``-DABC_DIR`` points at an existing ABC build, which is how to work on
the ``stp/abc`` fork -- see :doc:`code-guide`.

mimalloc is the exception: STP configures its build rather than
consuming its output, so it is fetched with CMake's FetchContent, which
downloads during configuration so that ``add_subdirectory`` has
something to descend into. ``-DFETCHCONTENT_SOURCE_DIR_MIMALLOC``
names an existing checkout.

The command-line parser `CLI11 <https://github.com/CLIUtils/CLI11>`__ and
the header-only floating-point library
`SymFPU <https://github.com/martin-cs/symfpu>`__ are headers and nothing
more; ``CLI11_DIR`` and ``SYMFPU_INCLUDE_DIRS`` name existing copies.

One is not vendored: `LibBF <https://bellard.org/libbf/>`__, which
converts the real literals in floating-point input --
``((_ to_fp 8 24) RNE 1.5)``. It is required, and there are three ways to
get it, tried in this order:

-  ``-DLIBBF_DIR=<path>`` naming a directory that holds ``libbf.h`` and a
   built ``bf`` library. It defaults to ``deps/libbf``, which is where
   an earlier build put one
-  an installed copy, found the way any library is -- including one that
   an earlier build installed into ``STP_DEP_DIR`` (see below)
-  ``-DENABLE_AUTO_DOWNLOAD=ON``, which clones
   `stp/libbf <https://github.com/stp/libbf>`__ at a pinned commit and
   builds it as part of this build, with this build's compiler and flags

Without any of the three, configuration fails and says so. An offline
build wants the first.

Upstream LibBF publishes release tarballs and no git repository, which is
what ``stp/libbf`` is for. It is laid out like STP's ABC fork: ``master``
holds the release tarballs verbatim, one commit each, and ``stp`` -- the
branch the pin names -- adds STP's MSVC portability changes on top. Moving
to a newer release means importing its tarball there and rebasing ``stp``
onto it, then moving the pin here.

SAT backends
------------

CaDiCaL is the default backend: it is the one enabled when nothing is
said, it needs no system library, and the build can produce one itself.
The others are asked for by name.

CryptoMiniSat used to be linked in whenever it happened to be installed.
It no longer is -- a build whose set of backends depends on what the
machine has lying around cannot be reproduced from its flags. Ask for it
with ``-DUSE_CRYPTOMINISAT=ON``, which also makes a missing one a
configuration error; ``-DUSE_CRYPTOMINISAT=AUTO`` restores the old
"use it if it is there" behaviour by name. It is found when installed,
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

It is the one dependency STP does not build for you: it reaches the build
as a CMake package rather than as a header and a library, and an
ExternalProject would write that package only after the configure that
has to read it. Install it, or run the script.

CaDiCaL is what you get by default, and is worth having on hard
bitvector problems. With
``-DENABLE_AUTO_DOWNLOAD=ON`` there is nothing to do but ask for it;
otherwise an installed CaDiCaL is found the way any library is, or
``CADICAL_DIR`` points at a checkout:

.. code-block:: bash

    git clone https://github.com/arminbiere/cadical
    cd cadical
    git checkout rel-3.0.1
    ./configure -fPIC
    make

Then configure STP with ``-DUSE_CADICAL:BOOL=ON -DCADICAL_DIR:PATH=<path>``,
where ``<path>`` is the checkout containing ``src/cadical.hpp`` and
``build/libcadical.a``. ``-fPIC`` is required, because ``libcadical.a``
is linked into STP's shared library. 

Whichever way it arrives, STP works out which CaDiCaL it has: a checkout
carries a ``VERSION`` file, and an installed copy is asked directly, by
compiling and running ``CaDiCaL::Solver::version()``. That decides
whether ``--cadical-factor`` can be compiled in, and the answer is
printed at configure time.

Enabling CaDiCaL makes it the default for that build, in place of
CryptoMiniSat; ``--cryptominisat`` (or ``--minisat``, in a
``-DUSE_MINISAT`` build) selects another backend at run time. With a
CaDiCaL 3.x build, ``--cadical-factor`` controls CaDiCaL's bounded
variable addition: ``on`` -- the default -- ``off``, or ``auto``, which
enables it only for problems with array operations. ``auto`` was the
default until bounded variable addition was measured on bitvector-only
problems and found to pay there too.

MiniSat is optional and off by default; enable it with
``-DUSE_MINISAT:BOOL=ON``, which also needs zlib -- MiniSat reads gzipped
DIMACS and says so in its public headers, so configuration fails without
it. With ``-DENABLE_AUTO_DOWNLOAD=ON`` there is nothing else to do: STP
clones and builds `stp/minisat <https://github.com/stp/minisat>`__ at a
pinned commit, which is an updated fork of a MiniSat that has not been
touched upstream since 2010 and no longer compiles as it stands. Your
distribution's minisat package works too, as does one built by hand:

.. code-block:: bash

    git clone https://github.com/stp/minisat
    cd minisat
    mkdir build && cd build
    cmake ..
    cmake --build . -j$(nproc)
    sudo cmake --install .
    command -v ldconfig && sudo ldconfig

The CryptoMiniSat recipe above is pre-configured in
``scripts/deps/setup-cms.sh``, which installs into ``deps/install`` --
searched without any extra flags. It is the only such script left: every
other dependency is now fetched and built by the build itself.

The Riss solver can be enabled with ``-DUSE_RISS``. Either point
``-DRISS_DIR=<path>`` at a Riss checkout that contains
``riss/core/Solver.h`` and ``build/lib/libriss-coprocessor.a`` --
or configure with
``-DENABLE_AUTO_DOWNLOAD=ON`` and let STP build it. Riss needs flags of
its own either way: it does not compile warning-free under current
compilers and does not build as C++17, so STP builds it with ``-w`` and
``-std=gnu++14``, and takes its headers as system headers so that a
``WERROR`` build does not fail inside them.

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

Floating-point support is always built, backed by SymFPU. STP carries
four fixes to it that upstream has not taken; they are applied to the
copy the build fetches, so there is nothing to do. An existing clone can
be used instead, via ``-DSYMFPU_INCLUDE_DIRS=<directory containing the
clone>`` -- that one is taken as-is, so it must already carry those
fixes, which are in ``cmake/deps-utils/symfpu``.

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
-  ``ENABLE_ASSERTIONS`` -- build with assertions. Three-valued: ``ON``
   and ``OFF`` are honoured as given, and if it is left unset the build
   type decides -- off for ``Release``, on for everything else. It used to
   be a plain on/off flag that ``Release`` overrode unconditionally, so
   ``-DENABLE_ASSERTIONS=ON -DCMAKE_BUILD_TYPE=Release`` silently produced
   a build without them; it now produces an asserting Release build
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
-  ``USE_CRYPTOMINISAT`` -- ``ON`` requires CryptoMiniSat 5.11 or newer and
   fails configuration if it is missing or older, ``AUTO`` uses it when a
   new enough one happens to be installed, and ``OFF`` -- the default --
   never uses it. (It replaces
   ``NOCRYPTOMINISAT`` and ``FORCE_CMS``, both of which are still accepted
   and warn)
-  ``USE_CADICAL`` and ``CADICAL_DIR`` -- build the CaDiCaL backend
   (on by default), optionally against a named checkout
-  ``USE_MINISAT`` -- build the MiniSat backend
-  ``USE_RISS`` -- build the Riss backend
-  ``TUNE_NATIVE`` -- build with ``-mtune=native``
-  ``WERROR`` -- treat compiler warnings as errors
-  ``BUILD_MANPAGE`` -- build and install the ``stp(1)`` manpage, which
   needs help2man. Three-valued: ``ON`` requires help2man and fails
   configuration without it, ``OFF`` never builds the page, and if it is
   left unset the page is built when help2man happens to be installed.
   Packagers who need the page either present or absent for certain should
   say which
-  ``SYMFPU_INCLUDE_DIRS`` -- build against an existing SymFPU clone
   rather than fetching one (point it at the directory *containing* the
   clone)
-  ``CLI11_DIR`` -- build against an existing CLI11 rather than fetching
   one
-  ``LIBBF_DIR`` -- where to find an already-built LibBF
-  ``ENABLE_AUTO_DOWNLOAD`` -- download and build dependencies that were
   not found, rather than failing. Off by default: a build that reaches
   the network should be asked to
-  ``STP_DEP_DIR`` -- where dependencies this build downloads are
   installed, and where dependencies are looked for. It defaults to
   ``<build>/deps/install``, so a build directory is self-contained.
   Point several build directories at one path and only the first pays
   to build anything: the rest find what it installed and download
   nothing, so they do not even need ``ENABLE_AUTO_DOWNLOAD``. To fill
   such a directory ahead of time, configure one build with
   ``-DSTP_DEP_DIR=<path> -DENABLE_AUTO_DOWNLOAD=ON`` and build its
   ``deps`` target, which builds the dependencies and nothing else.

   Only the *installed* dependencies are shared. ExternalProject's own
   scratch and stamp files stay in the build directory, so two builds
   sharing a path cannot corrupt each other's state -- though a shared
   directory does hold one copy of each library, whatever compiled it,
   and STP warns when the compiler or sanitizer settings that filled it
   differ from the ones now building against it
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

Working across several worktrees
--------------------------------

Working on STP usually means several branches alive at once, and a ``git
worktree`` each is the pleasant way to hold them: every worktree is a real
checkout with its own build directory, so branches do not disturb each
other and a long build is never invalidated by switching branch.

.. code-block:: bash

    git worktree add ../my-feature -b my-feature

The catch is that a fresh worktree looks like a fresh machine to the
build. None of the dependencies live inside the repository any more, so
a naive worktree downloads and rebuilds all of them. Two caches prevent
that, and they are separate because the dependencies come in two kinds.

``STP_DEP_DIR``, described above, holds the ones STP *links*.
``FETCHCONTENT_BASE_DIR`` holds the ones it *compiles*:
``unordered_dense``, mimalloc, googletest and OutputCheck. Share that one
for the download only, and read the note on it below before pointing two
build trees at the same one: FetchContent builds a dependency inside the
base directory too, so sharing it shares more than the download.

Warm both once:

.. code-block:: bash

    export STP_DEP_DIR=~/.cache/stp/deps          # configure.sh honours this
    cmake -S . -B warm -G Ninja \
      -DSTP_DEP_DIR=$STP_DEP_DIR \
      -DFETCHCONTENT_BASE_DIR=~/.cache/stp/fetch \
      -DENABLE_AUTO_DOWNLOAD=ON
    cmake --build warm --target deps

then in every worktree:

.. code-block:: bash

    cmake -S . -B build -G Ninja \
      -DSTP_DEP_DIR=$STP_DEP_DIR \
      -DFETCHCONTENT_BASE_DIR=~/.cache/stp/fetch \
      -DENABLE_AUTO_DOWNLOAD=ON \
      -DCMAKE_C_COMPILER_LAUNCHER=ccache -DCMAKE_CXX_COMPILER_LAUNCHER=ccache

``ENABLE_AUTO_DOWNLOAD=ON`` is still wanted even though everything is
already local, because a pinned revision can move under you and this is
what says the build may go and get it. To promise that it will not, leave
it off and pass ``-DFETCHCONTENT_FULLY_DISCONNECTED=ON`` instead: CMake
then skips the download and update steps outright, and a moved pin
becomes an error rather than a download. Nothing is re-fetched either
way -- against a warm base directory the ``*-src`` trees are not touched.

Sharing the compilation
~~~~~~~~~~~~~~~~~~~~~~~

A compiler launcher is worth setting, but on its own it shares nothing
between worktrees. STP compiles with ``-g``, and ccache hashes the
absolute path of the source when debug information is on, so the same
file in two worktrees hashes differently. Measured on one machine,
building an identical tree from a second worktree:

=========================================================  ===================
Setting                                                    Cross-worktree hits
=========================================================  ===================
``CMAKE_<LANG>_COMPILER_LAUNCHER=ccache`` alone            0 / 282 (0%)
plus ``CCACHE_BASEDIR`` and ``CCACHE_NOHASHDIR``           131 / 141 (93%)
=========================================================  ===================

which took that second build from 26s to 9s. So set them once, for the
directory the worktrees live under:

.. code-block:: bash

    export CCACHE_BASEDIR=~/clones/stp    # the parent of your worktrees
    export CCACHE_NOHASHDIR=1

``CCACHE_BASEDIR`` only rewrites paths *below* it, so keep the build
directory inside the worktree (``-B build``) rather than off in ``/tmp``,
or the include paths are left alone and the hits do not come.

The trade is that a cached object's debug information names the directory
of whichever worktree compiled it first. For everyday work that is a fair
price; before debugging something subtle, build that worktree with the
launcher off.

What invalidates a shared directory
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One ``STP_DEP_DIR`` holds one copy of each library, whatever compiled it.
STP records what filled it in ``.stp-dep-config`` and warns when the
compiler, sanitizer, toolchain or ABC ABI settings differ from the build
now using it. An ASan build in particular wants a directory of its own.

The build type is deliberately not recorded, except on MSVC: sharing a
differently-optimised ABC is a choice rather than a fault, but on MSVC
the runtime library follows the build type and mixing them does not link.

``FETCHCONTENT_BASE_DIR`` has no such stamp, and it wants more care than
``STP_DEP_DIR`` does. The dependencies STP compiles are added with
``add_subdirectory``, and FetchContent builds those in
``<base>/<name>-build``, so sharing the base directory shares the *build*
rather than only the download. Two build trees whose compiler or build
type differ then own the same object directory, and each recompiles all
of mimalloc the next time it is built -- a gcc tree and a clang tree
pointed at one base directory leave each other 37 steps to redo on every
alternation, indefinitely. This is not a race that running them one after
another avoids: both builds legitimately own the path they were given.

Share the sources and keep the builds apart instead. Give each build tree
its own base directory, and point each fetched source at one copy:

.. code-block:: bash

    cmake -S . -B build -G Ninja \
      -DFETCHCONTENT_BASE_DIR=$PWD/build/_deps \
      -DFETCHCONTENT_SOURCE_DIR_MIMALLOC=~/.cache/stp/fetch/mimalloc-src \
      -DFETCHCONTENT_SOURCE_DIR_UNORDEREDDENSE=~/.cache/stp/fetch/unordereddense-src

Name only the sources that exist: ``FETCHCONTENT_SOURCE_DIR_*`` pointed at
a directory that is not there fails the configure rather than falling back
to downloading it.

Tests across worktrees
~~~~~~~~~~~~~~~~~~~~~~

``ENABLE_TESTING=ON`` also needs lit, which is not a fetched dependency:
it is pip-installed into a virtual environment inside the build
directory, so it is per-build-tree and none of the above shares it. An
installed lit is used if there is one. Otherwise, when configuring with
``FETCHCONTENT_FULLY_DISCONNECTED=ON`` and no ``ENABLE_AUTO_DOWNLOAD``,
point ``LIT_TOOL`` at one -- the warm build's copy will do:

.. code-block:: bash

    -DLIT_TOOL=$PWD/warm/venv/bin/lit


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
``-DUSE_CRYPTOMINISAT=OFF``, CryptoMiniSat not being buildable there.

``windows (cadical, MinGW)`` is the one to follow for a solver to use: it
builds CaDiCaL under MinGW/UCRT64 and links a fully static ``stp.exe``
against it. ``windows (minisat, MSVC)`` builds with Visual Studio instead,
where MiniSat is the only backend that compiles.

Testing
-------

See :doc:`testing`.
