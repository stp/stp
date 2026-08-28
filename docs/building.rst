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

CryptoMiniSat and CaDiCaL together
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Enabling both is supported, and needs one thing said about it, because
CryptoMiniSat 5.14 and later fetch, build and *install* a CaDiCaL of their
own -- currently the meelgroup fork at 2.1.3. Its prefix therefore holds a
``libcadical.a``, a ``cadical/cadical.hpp`` and a CMake package under the
same names STP's own CaDiCaL uses.

Do not put it in ``deps/install``, which is where ``setup-cms.sh`` writes
by default and where STP keeps its own dependencies. Give CryptoMiniSat a
prefix of its own and name it, which is two extra arguments -- the script
forwards trailing ones to CMake, so its install prefix is overridable like
any other default:

.. code-block:: bash

    ./scripts/deps/setup-cms.sh -DBUILD_SHARED_LIBS=ON \
      -DCMAKE_INSTALL_PREFIX=$PWD/deps/cms-install

    cmake -S . -B build -DUSE_CADICAL=ON -DUSE_CRYPTOMINISAT=ON \
      -Dcryptominisat5_DIR=$PWD/deps/cms-install/lib/cmake/cryptominisat5

Sharing the one directory goes wrong in two independent ways, which is why
this is worth the two arguments.

``deps/install`` is ``STP_DEP_DIR``. Its include directory is a usage
requirement of every dependency STP builds, so it reaches the compile line
of nearly every file in the project -- and CryptoMiniSat's
``cadical/cadical.hpp`` sitting in it then shadows the one STP means to
use. There is no include order that fixes that: the two directories arrive
from different targets, so which comes first varies from target to target.
``include/stp/Sat/Cadical.h`` refuses to compile rather than let this pass
silently, so you get an error naming the cause.

``deps/install`` is also on ``CMAKE_PREFIX_PATH`` unconditionally, so that
the other ``scripts/deps/*.sh`` are found without flags. STP's own CaDiCaL
lookup therefore reaches the bundled copy, finds it, and stops -- building
against 2.x with ``--cadical-factor`` silently gone. ``CADICAL_DIR`` pins
that one lookup past it, and is worth passing if you have a checkout to
point at, but it does nothing about the shadowing above.

``stp --version`` reports the version of each backend actually linked, so
it is the quickest way to confirm which CaDiCaL you ended up with.

One combination is refused rather than arranged: a *static*
``libcryptominisat5`` puts its bundled CaDiCaL on STP's link line
alongside STP's, and the two sets of symbols collide. Build CryptoMiniSat
shared (``scripts/deps/setup-cms.sh -DBUILD_SHARED_LIBS=ON``), which keeps
its CaDiCaL inside the ``.so``. Or, if it must be static, have STP use the
very same archive so there is only one --
``-DCADICAL_LIBRARY=<cms prefix>/lib/libcadical.a
-DCADICAL_INCLUDE_DIR=<cms prefix>/include``, with ``CADICAL_DIR`` unset --
at the cost of the 3.x features. The configure error spells out all three.

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
-  ``TUNE_NATIVE`` -- build with ``-mtune=native``
-  ``ENABLE_LTO`` -- optimise across translation units, and across STP
   and the dependencies it compiles. Off by default. On its own it is
   worth about a percent; most of its value is in what it lets a profile
   do, and the two are covered together in `Link-time and
   profile-guided optimisation`_
-  ``PGO`` and ``PGO_DIR`` -- ``generate`` or ``use``, and where the
   profile lives. ``scripts/pgo-build.sh`` runs both passes with a
   training run in between; the same section has the detail
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

Link-time and profile-guided optimisation
-----------------------------------------

Two optimisations that are off by default and want to be turned on
together. Neither changes what STP computes; both change how long it
takes to compute it.

``-DENABLE_LTO=ON`` optimises across translation units. It reaches the
dependencies as well as STP itself, which is the point: most of a hard
query's time is not spent in ``libstp`` at all. On a ten-second QF_BV
query, ``CaDiCaL::Internal::propagate()`` alone is a quarter of the
instructions retired, and CaDiCaL as a whole is most of the rest.

``-DPGO=generate`` then ``-DPGO=use`` compiles twice, with a run of the
first build in between to record which branches are taken and which code
is hot. ``scripts/pgo-build.sh`` does all of it -- configure, build,
train, configure, build:

.. code-block:: bash

   CC=clang CXX=clang++ ./scripts/pgo-build.sh release --lto --ninja --auto-download

Options it does not recognise go to ``configure.sh``, so the build is
configured as usual. ``--train=PATH`` names what to train on, and may be
repeated; it defaults to ``tests/query-files``, the query suite in the
source tree.

What it is worth
~~~~~~~~~~~~~~~~

Measured over 726 SMT-LIB queries (QF_BV, QF_ABV, QF_FP, QF_BVFP,
QF_ABVFP; 20-core Xeon, each configuration run interleaved with the
others on a pinned core, best of three), against the same compiler's
plain ``release`` build:

=====================  ==============  ==============
Configuration          clang 21        gcc 13
=====================  ==============  ==============
``--lto``              -1.0%           -1.0%
``--pgo``              -3.7%           -1.5%
both                   -5.4%           -3.8%
=====================  ==============  ==============

as the geometric mean of the per-query change, which weights a
millisecond query and a ten-second one alike. Summed instead, so that the
hard queries dominate, clang with both is 7% faster and gcc with both is
1% faster: gcc's profile pays off on the front end, where a small query
spends its time, and hardly at all inside CaDiCaL's search, where a large
one does.

The split is sharper still on queries that are entirely CaDiCaL. Over 57
of them taking 12 to 123 seconds each, clang with both keeps its 4% --
4.2% on the geometric mean, 4.4% at the median query -- and gcc with both
has nothing left, at 0.1% on the median query.

Instructions retired fall by more than the time does -- 6.2% for gcc with
both, over the same queries under callgrind. That gap is the honest shape
of the result: PGO removes work, and what remains is increasingly waiting
on memory rather than executing.

Training on tests/query-files
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The default training set is the test suite, which takes about fifteen
seconds to run and needs nothing downloaded. It is not a compromise.
Trained instead on a disjoint sample of 443 SMT-LIB queries, on 60
deliberately hard ones, or on both corpora together, the same build lands
within half a percent of it either way -- and which of them is ahead
changes with the compiler and with the run. The profile is being used to
decide inlining and code layout, and a small query exercises the same
code as a large one, just less of it.

Two things do matter more than the training set:

-  **GCC needs** ``-fprofile-partial-training``, which the build passes
   for it. Without it, code the training run never reached is optimised
   for size, and a run of ``tests/query-files`` leaves most of CaDiCaL's
   search cold. Turning it off cost 0.8% of the 3.8% above.
-  **Clang wants the IR instrumentation**, ``-fprofile-generate``, which
   is what the build uses -- not the frontend's
   ``-fprofile-instr-generate``, which measured 1.5% worse here.

Which linker
~~~~~~~~~~~~

With clang, it makes a difference of its own. The same objects, a
bytecode-for-bytecode identical ``.text`` and an identical exported
symbol set, linked three ways: through lld the heaviest queries ran about
2% faster than through GNU ld or mold -- 2% at the median of the queries
over three seconds, up to 15% on individual ones. That is code layout,
and it is the one part of this that nothing in the source tree controls.

lld is also required rather than merely preferable for the ``generate``
pass. Clang finds its counters through ``__start___llvm_prf_*`` symbols
that the linker synthesises; under ThinLTO the sections they refer to do
not exist until the LTO backend has run, and GNU ld decides the symbols
before that, so a target whose inputs are all bytecode -- which, with
``--testing``, several of the unit tests are -- fails to link:

.. code-block:: text

   undefined reference to `__start___llvm_prf_names'

``pgo-build.sh`` therefore links with lld when the compiler is clang and
``ld.lld`` is installed, unless a linker was named on its command line.

Caveats
~~~~~~~

-  Both passes have to use the same build directory. GCC names each
   ``.gcda`` after the absolute path of the object file it came from, so
   a profile collected in one build directory is invisible from another.
   ``pgo-build.sh`` reconfigures in place for exactly this reason.
-  The dependencies are rebuilt between the passes, since they are
   compiled with the profile too. ``pgo-build.sh`` therefore keeps them
   in the build directory and refuses ``--dep-dir``.
-  ``ENABLE_LTO`` requires that ``CC`` and ``CXX`` be the same compiler
   at the same version. Without LTO a mismatched pair -- which is what a
   machine whose ``cc`` is gcc 15 and whose ``g++`` is gcc 11 has --
   builds STP quite happily; with it they exchange bytecode, and the
   build fails at the end with ``bytecode stream ... generated with LTO
   version 15.1 instead of the expected 11.3``. Configuration checks for
   this and stops first.
-  A profile is not portable and not reproducible: it belongs to one
   source tree and one compiler version, and two training runs of the
   same build do not produce byte-identical binaries. For a build that
   has to be reproducible, leave ``PGO`` off. ``ENABLE_LTO`` on its own
   is deterministic.

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

Doing all of this by hand
~~~~~~~~~~~~~~~~~~~~~~~~~

Nothing above needs a tool: the flags are the whole of it, and they are
written out so that they can be typed, scripted or put in a
``CMakeUserPresets.json``, whichever suits.

If a shell function is what suits, `stp.sh <https://github.com/stp/stp.sh>`__
is a set of bash and zsh helpers that apply exactly these flags -- one
command to warm the caches, one to make a worktree, one to build it. It is a
convenience kept alongside STP rather than part of it, and it is not what the
rest of this page assumes: everything here works without it, and on the
platforms it does not cover.


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

Building on Windows
-------------------

Two toolchains are built and tested: Visual Studio's ``cl``, and the MSYS2
UCRT64 gcc. Which SAT backend you get follows from which one you pick.
Under MSVC that is MiniSat; under MinGW it is CaDiCaL, whose own
``BUILD.md`` documents a MinGW build. CryptoMiniSat is not built on
Windows at all -- upstream supports MinGW there, and STP does not package
it -- so both configure with ``-DUSE_CRYPTOMINISAT=OFF``.

Everything else is fetched. ``-DENABLE_AUTO_DOWNLOAD=ON`` builds ABC,
LibBF, SymFPU, CLI11 and the SAT backend as part of the build, with its
compiler and its flags, so the toolchain, flex, bison and -- for MiniSat
-- a zlib are all that has to be installed beforehand.

Both use the Ninja generator rather than the Visual Studio one. Ninja
parallelises by default, where MSBuild without ``/m`` builds one project
at a time, and it honours ``CMAKE_<LANG>_COMPILER_LAUNCHER``, which the
Visual Studio generator ignores silently, so a compiler cache does
nothing there. The cost is that Ninja does not locate the MSVC toolchain
for itself: start from an *x64 Native Tools* developer prompt, or enter
the developer shell first.

The two CI jobs -- ``windows (minisat, MSVC)`` and
``windows (cadical, MinGW)`` in
`.github/workflows/ci.yml <https://github.com/stp/stp/blob/master/.github/workflows/ci.yml>`__
-- do exactly what is below, and are the reference if a detail here is
not enough.

Visual Studio
~~~~~~~~~~~~~

flex and bison do not come with Visual Studio.
`winflexbison <https://github.com/lexxmark/winflexbison>`__ supplies
``win_flex.exe`` and ``win_bison.exe``, which are the names CMake's
``FindFLEX`` and ``FindBISON`` look for on Windows. Put its directory on
``PATH`` and keep the extracted ``data/`` beside the executables, since
bison finds its skeleton files relative to its own path.

MiniSat's public headers include ``zlib.h``, so a zlib is needed too --
vcpkg's ``zlib:x64-windows-static``, for one. Name the include directory
and the library file rather than reaching for ``ZLIB_ROOT``: vcpkg
installs that library as ``zs.lib``, which is not one of the names
``FindZLIB`` searches for. What STP resolves is passed on to MiniSat's
own build, which searches the default paths only, so one setting covers
both.

.. code-block:: bat

    set ABC_USE_NO_PTHREADS=1

    cmake -B build -G Ninja ^
      -DCMAKE_BUILD_TYPE=RelWithDebInfo ^
      -DENABLE_AUTO_DOWNLOAD=ON ^
      -DSTATICCOMPILE=ON ^
      -DUSE_MINISAT=ON -DUSE_CRYPTOMINISAT=OFF -DUSE_CADICAL=OFF ^
      -DENABLE_PYTHON_INTERFACE=OFF ^
      -DZLIB_INCLUDE_DIR=C:/vcpkg/installed/x64-windows-static/include ^
      -DZLIB_LIBRARY=C:/vcpkg/installed/x64-windows-static/lib/zs.lib ^
      .
    cmake --build build

``ZLIB_LIBRARY`` names the ``.lib`` itself, and vcpkg has not always
spelled it the same way, so look in that ``lib\`` directory rather than
copying the line verbatim.

``ABC_USE_NO_PTHREADS`` is read by ABC's makefile while CMake configures.
Without it ABC's threaded paths are compiled, and they do not build with
``cl``.

If a compiler cache is pointed at the build, add
``-DCMAKE_POLICY_DEFAULT_CMP0141=NEW`` and
``-DCMAKE_MSVC_DEBUG_INFORMATION_FORMAT=Embedded``. The default ``/Zi``
writes a program database shared by every translation unit, which is
neither cacheable nor safe to write from several compilations at once;
those two move the build onto ``/Z7``.

MinGW (MSYS2 UCRT64)
~~~~~~~~~~~~~~~~~~~~

From a UCRT64 shell:

.. code-block:: bash

    pacman -S --needed bison flex git make \
        mingw-w64-ucrt-x86_64-cmake \
        mingw-w64-ucrt-x86_64-gcc \
        mingw-w64-ucrt-x86_64-ninja

    export ABC_USE_NO_PTHREADS=1
    export ABC_USE_STDINT_H=1

    cmake -B build -G Ninja \
        -DENABLE_AUTO_DOWNLOAD=ON \
        -DSTATICCOMPILE=ON \
        -DUSE_CADICAL=ON -DUSE_CRYPTOMINISAT=OFF \
        -DENABLE_PYTHON_INTERFACE=OFF \
        .
    cmake --build build --parallel "$(nproc)"

``ABC_USE_STDINT_H`` is the one that is easy to miss. ABC's architecture
probe reads eight-byte pointers as 64-bit Linux and picks an integer type
that is 32 bits wide under LLP64, and the pointer casts in its headers
then do not compile; the variable routes them onto ``stdint.h`` instead.
``ABC_USE_NO_PTHREADS`` is as above.

CaDiCaL needs nothing extra here: ``cmake/FindCaDiCaL.cmake`` drives its
configure script and builds the library alone, which is what this
toolchain needs it to do.

Common to both
~~~~~~~~~~~~~~

-  Ninja puts the binary at the top of the build tree: ``build\stp.exe``.
-  ``-DSTATICCOMPILE=ON`` produces an ``stp.exe`` that needs nothing
   beside it. Under MSVC it also moves STP *and its dependencies* onto
   the static CRT, so a dependency directory filled by one choice cannot
   be linked into a build that wants the other. STP records what filled
   ``STP_DEP_DIR`` and warns when a later build disagrees.
-  The Python interface is off in both jobs and is not exercised on
   Windows.
-  Neither job runs the lit suite; both run a handful of queries through
   the binary they built. ``-DENABLE_TESTING=ON`` is correspondingly less
   well trodden there.

Testing
-------

See :doc:`testing`.
