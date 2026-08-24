# Developer notes

Notes for people working *on* STP rather than building it once. For a plain
build, `README.markdown` and `docs/building.rst` are the right places; this
file is about keeping many builds cheap.

## Use worktrees

STP is one repository with a lot of concurrent lines of work, and a `git
worktree` per branch is much the nicest way to hold them. Each worktree is a
real checkout with its own build directory, so branches do not disturb each
other, a long build is never invalidated by switching branch, and you can have
a bisect, a review and a feature build all alive at once.

```sh
git worktree add ../my-feature -b my-feature
```

The catch is that a fresh worktree looks like a fresh machine to the build:
none of STP's dependencies are inside the repository any more -- they are
fetched at pinned revisions -- so a naive worktree re-downloads and rebuilds
everything. Everything below is about not doing that.

## Share the dependencies

There are two caches, and they are separate because the dependencies come in
two kinds.

`STP_DEP_DIR` is where the dependencies STP *links* are installed: ABC, LibBF,
SymFPU, CLI11, and whichever SAT solvers are enabled. Point several build
directories at one and only the first pays to build anything; the rest find
what it installed and declare no ExternalProject at all.

`FETCHCONTENT_BASE_DIR` is where the dependencies STP *compiles* are unpacked:
`unordered_dense`, mimalloc, googletest, OutputCheck. Sharing it saves the
download, not the compile -- mimalloc and googletest are added to the build
with `add_subdirectory`, so they are compiled once per build directory whatever
you do.

Warm both once:

```sh
export STP_DEP_DIR=~/.cache/stp/deps          # configure.sh honours this
cmake -S . -B warm -G Ninja \
  -DSTP_DEP_DIR=$STP_DEP_DIR \
  -DFETCHCONTENT_BASE_DIR=~/.cache/stp/fetch \
  -DENABLE_AUTO_DOWNLOAD=ON
cmake --build warm --target deps              # builds the dependencies, nothing else
```

Then in every worktree:

```sh
cmake -S . -B build -G Ninja \
  -DSTP_DEP_DIR=$STP_DEP_DIR \
  -DFETCHCONTENT_BASE_DIR=~/.cache/stp/fetch \
  -DENABLE_AUTO_DOWNLOAD=ON \
  -DCMAKE_C_COMPILER_LAUNCHER=ccache -DCMAKE_CXX_COMPILER_LAUNCHER=ccache
```

`ENABLE_AUTO_DOWNLOAD=ON` is still wanted here even though everything is
already local, because a pinned revision can move under you and this is what
says the build may go and get it. If you would rather promise it will not,
leave it off and pass `-DFETCHCONTENT_FULLY_DISCONNECTED=ON` instead: CMake
then skips the download and update steps outright, and a moved pin becomes an
error rather than a download. Nothing is re-fetched either way -- with a warm
base directory the `*-src` trees are not touched.

## Share the compilation

A compiler launcher is worth setting, but on its own it does **not** share
anything between worktrees. STP compiles with `-g`, and ccache hashes the
absolute path of the source when debug information is on, so the same file in
two worktrees hashes differently. Measured on one machine, building an
identical tree from a second worktree:

| Setting | Cross-worktree hits |
| --- | --- |
| `CMAKE_<LANG>_COMPILER_LAUNCHER=ccache` alone | 0 / 282 (0%) |
| plus `CCACHE_BASEDIR` and `CCACHE_NOHASHDIR` | 131 / 141 (93%) |

which took that second build from 26s to 9s. So set them, once, for the
directory your worktrees live under:

```sh
export CCACHE_BASEDIR=~/clones/stp    # the parent of your worktrees
export CCACHE_NOHASHDIR=1
```

`CCACHE_BASEDIR` only rewrites paths *below* it, so keep the build directory
inside the worktree (`-B build`) rather than off in `/tmp`, or the include
paths will not be rewritten and you are back to missing.

The trade is that a cached object's debug information names the directory of
whichever worktree compiled it first. For everyday work that is a fair price;
if you are about to debug something subtle, build that worktree with the
launcher off.

## What invalidates a shared dependency directory

One `STP_DEP_DIR` holds one copy of each library, whatever compiled it. STP
records what filled it in `.stp-dep-config` and warns when the compiler,
sanitizer, toolchain or ABC ABI settings differ from the build now using it.
Take the warning seriously: an ASan build in particular wants a dependency
directory of its own.

Deliberately *not* recorded is the build type, on non-MSVC: sharing a
differently-optimised ABC is a choice, not a fault. MSVC is the exception,
because there the runtime library follows the build type and mixing them does
not link -- so it is recorded there.

`FETCHCONTENT_BASE_DIR` has no such stamp, and each configure rewrites the
`*-subbuild` scratch inside it. Two configures running against one base
directory *at the same time* can race; sequential use is fine.

## Tests

`ENABLE_TESTING=ON` also needs lit, which is not a fetched dependency: it is
pip-installed into a virtual environment inside the build directory, so it is
per-build-tree and shared by none of the above. If you have lit installed,
that is used. If you do not, and you are configuring with
`FETCHCONTENT_FULLY_DISCONNECTED=ON` and no `ENABLE_AUTO_DOWNLOAD`, point
`LIT_TOOL` at one -- the warm build's copy will do:

```sh
-DLIT_TOOL=$PWD/warm/venv/bin/lit
```
