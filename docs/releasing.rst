Making a release
================

There is no release branch, no changelog file, and no packaging step in
the build -- CPack was removed some time ago, so there is no
``make package`` target. A release is a version bump on master, a git
tag, and a GitHub release with a prebuilt binary attached.

Only the first of those is done by hand. Pushing the tag runs
``.github/workflows/release.yml``, which checks the version, builds the
binary and opens the release as a draft for you to look over and
publish. In short:

#. Edit the version in the two files below, and commit to master.
#. ``git tag 2.3.5 && git push origin 2.3.5``.
#. Read the draft release the workflow leaves behind, then publish it.

The rest of this page is what those steps rest on.

Where the version lives
-----------------------

Two files carry the version and both are edited by hand:

-  ``CMakeLists.txt`` -- ``set(STP_FULL_VERSION "2.3.4")``
-  ``docs/conf.py`` -- ``release = '2.3.4'``

Everything else is derived from ``STP_FULL_VERSION``. It is split on
``.`` into ``PROJECT_VERSION_MAJOR``, ``PROJECT_VERSION_MINOR`` and
``PROJECT_VERSION_PATCH``, which then feed:

-  ``include/stp/config.h`` -- ``STP_VERSION``, ``STP_VERSION_MAJOR``,
   ``STP_VERSION_MINOR``, from ``include/stp/config.h.in``.
-  ``lib/Util/GitSHA1.cpp`` -- ``get_git_version_tag()`` returns the full
   version string and ``get_git_version_sha()`` the commit hash, which is
   what ``stp --version`` prints. The hash is captured by CMake at
   *configure* time from the current HEAD, so configure after you have
   committed the bump if you want the released binary to name the release
   commit.
-  ``STPConfigVersion.cmake`` -- what ``find_package(STP 2.3.4)`` matches
   against in a downstream project.
-  ``stp.1`` -- the generated man page's version string.
-  ``libstp.so`` -- the ``VERSION`` and ``SOVERSION`` properties set in
   ``lib/CMakeLists.txt``.

Choosing the number
-------------------

The soname is ``MAJOR.MINOR`` only, and ``STPConfigVersion.cmake``
declares STP API-compatible only across a matching ``MAJOR.MINOR``. So:

-  A patch bump (2.3.4 to 2.3.5) keeps ``libstp.so.2.3``. Downstream
   packages and anything that linked against the previous release keep
   working.
-  A minor or major bump changes the soname and makes
   ``find_package(STP 2.3)`` stop matching. Distribution packagers have to
   rebuild everything that links STP, so bump the minor only when the API
   or ABI actually changed.

Before tagging
--------------

The version bump has to be committed and pushed to master before the tag
is pushed, since the workflow refuses to build a tag whose name does not
match the tree. Beyond that:

-  CI green on the commit you are about to tag, including the 32-bit job
   (``scripts/ci-32bit.sh``) and ``gcc (static)`` -- the latter runs the
   same steps the release build does, so it is the early warning for a
   release that would fail to build.
-  The tag on master, not on a feature branch. The workflow builds
   whatever the tag points at without checking where it sits.
-  Optionally a full test run locally. See :doc:`testing`;
   ``ENABLE_TESTING`` needs a shared-library build, so it cannot be
   combined with a static build -- these are two separate build
   directories. CI covers this, so it is a duplicate rather than a gap.

Tagging, which cuts the release
-------------------------------

Tags are lightweight and unprefixed since 2.3.1 -- ``2.3.1``, ``2.3.2``,
``2.3.3``, ``2.3.4``. (The older ``stp-2.2.0`` and the branch tags
``smtcomp2020`` and ``2.3.4_cadical`` are exceptions, not the pattern.)
The tag goes on an ordinary master commit; there is no separate "release"
commit beyond the version bump itself.

Pushing such a tag is the whole release procedure. It matches the
``[0-9]+.[0-9]+.[0-9]+`` filter in ``.github/workflows/release.yml``,
which builds the binary and opens a draft release:

.. code-block:: bash

    git tag 2.3.5
    git push origin 2.3.5

The workflow runs four jobs:

``check version``
   Reads ``STP_FULL_VERSION`` out of ``CMakeLists.txt`` and ``release``
   out of ``docs/conf.py``, and fails unless both equal the tag. This
   runs before anything is built, so a forgotten bump costs a minute
   rather than a published binary with the wrong version in it. If it
   fails, fix the version, delete and re-push the tag.

``linux-amd64``
   Builds the static binary and uploads it as a workflow artifact named
   ``stp-<version>-linux-amd64``. It uses the composite action under
   ``.github/actions/build-static-linux``, which is the same set of steps
   the ``gcc (static)`` CI job runs on every push -- so the binary that
   gets published is built the way CI has been testing all along, and a
   break in it shows up in normal CI rather than at release time.

``publish``
   Re-checks the asset after it has been through the artifact round-trip
   -- that it is static, and that ``--version`` reports the version being
   released -- then calls ``gh release create --draft --generate-notes``.

Nothing is public at the end of this. The release is a **draft**: not
listed, and the asset is not downloadable until you open it on the
Releases page and press publish. That is deliberate, and it is where the
remaining manual steps live:

-  Read the generated notes. ``--generate-notes`` produces the "What's
   Changed" list of merged pull requests since the previous release,
   which is what the 2.3.4 notes are. Edit them if the release deserves a
   summary at the top.
-  Tick "Set as a pre-release" if it is not meant to be the recommended
   download; 2.1.1 and 2.3.1 were released that way.
-  Press "Publish release".

Note that the release GitHub currently shows as latest is titled
``v2.3.4`` and points at the ``2.3.4_cadical`` branch tag rather than at
the ``2.3.4`` tag. That is an accident of how that one was cut, not
something to copy -- and the tag filter deliberately does not match names
like that, so pushing a branch tag will not cut a release.

What gets built
---------------

One asset: a statically linked Linux x86-64 binary, so someone can
download one file and run it without a matching glibc or any STP
libraries installed. The job asserts this (``ldd`` must fail on the
result) rather than assuming it.

The option that decides how portable it is is ``USE_POPCNT``, which is on by default and emits ``-mpopcnt``. That needs
Nehalem (2008) or Barcelona (2007) or later, which is a safe assumption
for a release download; build with ``-DUSE_POPCNT=OFF`` if you want to
support older hardware, and the software fallback in
``include/stp/Util/BitOps.h`` is used instead. ``TUNE_NATIVE`` is off by
default and only passes ``-mtune=native``, which affects instruction
scheduling rather than which instructions may be emitted, so it does not
make a binary unrunnable elsewhere -- but there is no reason to turn it
on for a build other people will run.

The build configures with ``NOCRYPTOMINISAT``, because CryptoMiniSat's
exported static link line pulls in GMP and other dependencies that are
not reliably available as archives on a runner. The released binary
therefore solves with MiniSat, which is worth being aware of: it is not
the solver STP performs best with.

Asset naming has not been consistent historically. 2.3.2 and 2.3.3 used
``stp-<version>-linux-amd64``, 2.3.3 also shipped a ``stp-win64.exe``,
and 2.3.4 shipped a bare ``stp`` plus a ``stp.tar`` containing just that
same binary. The workflow standardises on the first form: it says what it
is once it is in someone's downloads directory.

No Windows asset
~~~~~~~~~~~~~~~~

2.3.3 shipped a ``stp-win64.exe`` and the ``windows`` CI job still builds
one on every push, so producing it is not the obstacle. Publishing it is
the problem: MSVC compiles neither CryptoMiniSat nor CaDiCaL, both of
which use POSIX-only code, so a Windows build can only be linked against
MiniSat. That is slow enough that shipping it would misrepresent what STP
does. Getting a competitive solver to build on Windows -- via MinGW, or by
porting the POSIX-only parts -- comes before shipping a Windows binary
again.

Other platforms
~~~~~~~~~~~~~~~

Adding one is a job of about ten lines -- copy the ``linux-amd64`` job,
change ``runs-on`` to ``ubuntu-24.04-arm`` (free for public repositories)
and the asset suffix to ``linux-arm64``. macOS is possible but cannot be
linked fully statically, since it ships no static libc, so that asset
would carry runtime dependencies this one does not; no STP release has
shipped one.

Building it yourself
--------------------

You do not need CI to produce the same binary -- for testing the release
build, or if Actions is unavailable:

.. code-block:: bash

    mkdir build-static && cd build-static
    cmake -DSTATICCOMPILE=ON -DNOCRYPTOMINISAT=ON -DCMAKE_BUILD_TYPE=Release ..
    cmake --build . -j$(nproc)
    ./stp --version          # should print the new version and the tagged SHA
    ldd ./stp                # should say "not a dynamic executable"

Note that ``STATICCOMPILE`` needs a minisat built with ``STATICCOMPILE``
too -- the default minisat build installs only the shared library, and
the link then fails looking for ``libminisat.a``. Run
``./scripts/deps/setup-minisat.sh -DSTATICCOMPILE=ON`` first if that is
what you have.

Prefer the workflow for anything you intend to publish. It checks out the
tag, so the binary provably comes from the released commit rather than
from whatever is in your working tree -- which, with the submodules STP
compiles in, is easy to get wrong without noticing.

After the release
-----------------

-  Nothing needs pushing to downstream packagers: Debian, Homebrew, and
   the KLEE and Souper build scripts pick releases up themselves.
-  The exported CMake config -- what ``find_package(STP <version>)``
   resolves against -- is covered by the ``gcc (cadical)`` CI job, which
   installs STP and builds ``examples/simple`` against the install tree on
   every push. If that job was green on the tagged commit there is nothing
   further to check here.
-  Bump the version again only when the next release is cut. Master
   carries the last released version between releases, so a build from
   master reports the release it followed rather than something like
   ``2.3.5-dev``. That is the existing convention, not an oversight.
