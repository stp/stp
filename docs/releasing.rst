Making a release
================

A release is a version bump on master, a git tag, and a GitHub release
with a prebuilt binary attached. There is no release branch, no changelog
file, and no packaging step -- CPack was removed some time ago, so there
is no ``make package`` target.

Only the bump is done by hand. Pushing the tag runs
``.github/workflows/release.yml``, which checks the version, builds the
binary and opens the release as a draft:

#. Edit the version in the two files below, and commit to master.
#. ``git tag 2.4.2 && git push origin 2.4.2``.
#. Read the draft the workflow leaves behind, then publish it.

Where the version lives
-----------------------

Two files carry it, both edited by hand:

-  ``CMakeLists.txt`` -- ``set(STP_FULL_VERSION "2.4.1")``
-  ``docs/conf.py`` -- ``release = '2.4.1'``

Everything else derives from ``STP_FULL_VERSION``: ``include/stp/config.h``,
``STPConfigVersion.cmake``, the ``stp.1`` man page, the ``SOVERSION`` of
``libstp.so``, and what ``stp --version`` prints. That last also carries
the HEAD commit hash, captured at *configure* time -- so configure after
committing the bump if you want the binary to name the release commit.

The soname is ``MAJOR.MINOR`` only, and ``STPConfigVersion.cmake`` declares
STP compatible only across a matching ``MAJOR.MINOR``. A patch bump keeps
``libstp.so.2.4``, so downstream packages keep working; a minor or major
bump makes ``find_package(STP 2.4)`` stop matching and forces packagers to
rebuild everything that links STP. Bump the minor only when the API or ABI
actually changed.

Before tagging
--------------

-  The bump committed and pushed to master: the workflow refuses to build
   a tag whose name does not match the tree.
-  CI green on the commit you are about to tag. ``gcc (static, release)``
   is the one to watch -- it runs the release build's steps in the release
   build's configuration, so it is the early warning for a release that
   would fail to build.
-  The tag on master, not on a feature branch. The workflow builds
   whatever the tag points at without checking where it sits.

A local test run is optional and duplicates CI. Note that
``ENABLE_TESTING`` needs a shared-library build and so cannot be combined
with a static one -- see :doc:`testing`.

Tagging, which cuts the release
-------------------------------

Release tags are lightweight and unprefixed; ``stp-2.2.0`` is the only one
that ever carried a prefix. It and the
branch tags ``smtcomp2020`` and ``2.3.4_cadical`` are exceptions, and the
``[0-9]+.[0-9]+.[0-9]+`` filter deliberately does not match names like
them, so pushing a branch tag will not cut a release.

.. code-block:: bash

    git tag 2.4.2
    git push origin 2.4.2

That is the whole procedure. Three jobs follow:

``check version``
   Fails unless both version files equal the tag, before anything is
   built. If it fails, fix the version, delete and re-push the tag.

``linux-amd64``
   Builds and strips the binary and uploads it as an artifact, using the
   composite action under ``.github/actions/build-static-linux`` with the
   same inputs as the ``gcc (static, release)`` CI job -- so a break in the
   release build shows up in normal CI rather than here.

``publish``
   Re-checks the asset after the artifact round-trip: static, reporting the
   version *and the commit sha* being released, CryptoMiniSat compiled in,
   assertions not, and still solving after the strip. Then writes
   ``SHA256SUMS`` and calls ``gh release create --draft --generate-notes``.

A ``workflow_dispatch`` trigger runs everything except the release
creation, comparing the two version files against each other rather than
against a tag. Use it after changing ``release.yml`` or the composite
action, so the first execution of the change is not a real tag push.

Publishing the draft
~~~~~~~~~~~~~~~~~~~~

A **draft** release is unlisted and its assets are not downloadable until
you open it on the Releases page, which leaves the notes editable and a bad
build discardable before anyone has fetched it.

-  Read the generated notes: ``--generate-notes`` lists the pull requests
   merged since the previous release, which is what the 2.3.4 notes are.
   Add a summary if the release deserves one.
-  Tick "Set as a pre-release" if it is not the recommended download; 2.1.1
   and 2.3.1 went out that way.
-  Press "Publish release".

The release titled ``v2.3.4`` points at the ``2.3.4_cadical`` branch tag
rather than at the ``2.3.4`` tag -- an accident of how that one was cut,
not something to copy.

What gets built
---------------

One statically linked Linux x86-64 binary, so someone can download a single
file and run it without a matching glibc or any STP libraries installed --
asserted rather than assumed, by requiring ``ldd`` to fail on it. Beside it
go ``LICENSE`` and ``LICENSE_COMPONENTS``, and a ``SHA256SUMS`` covering all
three, checkable with ``sha256sum --check SHA256SUMS``. That
is integrity, not provenance: anyone able to replace the binary could
replace the sums file with it. Signing, or GitHub's build attestations,
would be the next step if that is ever wanted.

Asset naming has not been consistent historically -- 2.3.4 shipped a bare
``stp`` plus a ``stp.tar`` of the same binary -- so the workflow
standardises on ``stp-<version>-linux-amd64``, the form 2.3.2 and 2.3.3
used, which still says what it is once it is in a downloads directory.

Portability is decided by ``USE_POPCNT``, on by default, which emits
``-mpopcnt`` and so needs Nehalem (2008) or Barcelona (2007) or later: a
safe floor for a release download. ``-DUSE_POPCNT=OFF`` falls back to the
software implementation in ``include/stp/Util/BitOps.h``. ``TUNE_NATIVE``
is off, and affects only instruction scheduling in any case.

The solver
~~~~~~~~~~

Which solver a binary uses with no flag given is decided at compile time:
``UserDefinedFlags``'s constructor picks CaDiCaL, then CryptoMiniSat, then
Riss, then MiniSat, by whichever ``USE_*`` macro is defined. Linking
CryptoMiniSat in is therefore the whole of what makes this a CryptoMiniSat
release; there is no flag for users to remember.

CryptoMiniSat rather than CaDiCaL because its author has contributed to
STP, and STP ships his solver by preference. Note the consequence:
``USE_CADICAL`` is deliberately *not* enabled, since the order above would
then invert that preference silently -- enabling both is not a way to ship
both. CaDiCaL is in the binary regardless, as CryptoMiniSat 5.14 builds and
uses it internally.

Two configure arguments matter, and ``publish`` confirms both in the
finished binary rather than trusting the command line:

``-DUSE_CRYPTOMINISAT=ON``
   A ``find_package(cryptominisat5)`` that misses is otherwise silent --
   the build falls through and produces a working MiniSat binary.

``-DCMAKE_BUILD_TYPE=Release``
   ``CMakeLists.txt`` turns ``ENABLE_ASSERTIONS`` off only for an exact
   ``Release``, and the default is ``RelWithDebInfo``, so without this the
   published binary asserts on every query.

The static link also needs ``libgmp.a``, which CryptoMiniSat's config puts
on the link line, hence ``libgmp-dev`` in the action's package list. The
runner image happens to ship it already; the action names it rather than
assuming it.

Pinned revisions
~~~~~~~~~~~~~~~~

The release links CryptoMiniSat, pinned by ``setup-cms.sh`` at
``release/v5.14.7``, and minisat, pinned by commit since ``stp/minisat``
carries only upstream's 2.0 and 2.2.x tags. This matters more here than in
CI, because the workflow restores a dependency cache rather than rebuilding:
an unpinned dependency would mean linking against whatever a default branch
held when some earlier CI run populated that cache.
``scripts/deps/cache-key.sh`` hashes the setup scripts, so moving a pin
invalidates the cache.

Two things are not pinned. OutputCheck is resolved with ``git ls-remote`` on
every run, which is harmless -- it is a test-only tool that never gets
linked into anything. The CaDiCaL and cadiback that CryptoMiniSat fetches
and builds for itself are not pinned by anything: CryptoMiniSat takes them
from their default branches, so which revision arrives depends on the day,
and ``cache-key.sh`` does not track it. That one is a real gap, described at
the top of ``setup-cms.sh``. It is unrelated to
``cmake/FindCaDiCaL.cmake``, which pins ``rel-3.0.1`` and which the
release does not run.

``setup-cms.sh`` builds the solver stack in ``Release`` rather than CMake's
default, which had CryptoMiniSat compiling at ``-g -ggdb3`` and took the
static ``stp`` from 76M to 24M. The published asset is stripped either way,
so what this changes is the dependency tree, the CI cache and every
unstripped build -- at the cost of backtraces no longer resolving inside
CryptoMiniSat, CaDiCaL or cadiback. Pass
``-DCMAKE_BUILD_TYPE=RelWithDebInfo`` to the script to get that back.

What is not shipped
~~~~~~~~~~~~~~~~~~~

No Windows binary, though CI builds two and 2.3.3 shipped one. MSVC compiles
neither CryptoMiniSat nor CaDiCaL, both of which use POSIX-only code, so
``windows (minisat, MSVC)`` is left with MiniSat as its only backend -- slow
enough that shipping it would misrepresent what STP does. ``windows
(cadical, MinGW)`` no longer has that problem: it builds CaDiCaL under
MinGW/UCRT64 and links a fully static ``stp.exe`` against it, so publishing
that one is now a question of wiring it into the release workflow rather
than of getting a competitive solver to build.

No other architectures either, though adding a Linux one is about ten
lines: copy the ``linux-amd64`` job, change ``runs-on`` to
``ubuntu-24.04-arm`` (free for public repositories) and the asset suffix.
macOS cannot be linked fully statically, since it ships no static libc, so
that asset would carry runtime dependencies this one does not.

Building it yourself
--------------------

For testing the release build, or if Actions is unavailable:

.. code-block:: bash

    ./scripts/deps/setup-cms.sh
    mkdir build-static && cd build-static
    cmake -DSTATICCOMPILE=ON -DCMAKE_BUILD_TYPE=Release -DUSE_CRYPTOMINISAT=ON \
          -Dcryptominisat5_DIR=$PWD/../deps/install/lib/cmake/cryptominisat5 ..
    cmake --build . -j$(nproc)
    ./stp --version   # the new version and the tagged SHA, and both
                      # -DNDEBUG and -DUSE_CRYPTOMINISAT in COMPILE_DEFINES
    ldd ./stp         # "not a dynamic executable"

Neither setup script needs arguments: both already build the static PIC
libraries a static STP links against. Note that the configure line above does
not pass ``-DUSE_MINISAT=ON``, so it does not in fact link minisat --
``USE_MINISAT`` has defaulted to off since that backend became opt-in, and
the release workflow does not build MiniSat at all. Enable it only if
you want to reproduce a build that has MiniSat compiled in.

Prefer the workflow for anything you intend to publish: it checks out the
tag, so the binary provably comes from the released commit rather than from
whatever is in your working tree -- easy to get wrong with the dependencies
STP compiles in.

After the release
-----------------

-  Nothing needs pushing to downstream packagers: Debian, Homebrew, and the
   KLEE and Souper build scripts pick releases up themselves.
-  ``find_package(STP)`` is covered by the ``uf-install-tree-public-header-consumer``
   test, which installs STP into a staged prefix and then configures, builds
   and runs ``tests/api/install/uf-public-header-consumer`` against it. It runs
   wherever ``ENABLE_TESTING`` is on, including the ``gcc (cadical ...)`` CI
   jobs -- a matrix over the supported CaDiCaL tags -- on every push.
   The *version* half is not covered: no consumer asks for one, so
   ``STPConfigVersion.cmake`` is never consulted. If a release changes it,
   check it by hand with ``find_package(STP <version> REQUIRED)``.
-  Bump the version again only when the next release is cut. Master carries
   the last released version between releases, so a build from master
   reports the release it followed rather than something like
   ``2.4.2-dev``. That is the existing convention, not an oversight.
