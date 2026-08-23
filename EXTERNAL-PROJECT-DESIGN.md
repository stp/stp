# Migrating STP's dependencies to `ExternalProject_Add`

Design note for the `external_project` branch. Written against STP at
`3692e5d8` and cvc5 `main` as checked out in `~/clones/cvc5/main`.

The ask: adopt cvc5's dependency model — a `cmake/FindX.cmake` per dependency
that looks for a system copy and otherwise downloads and builds one with
`ExternalProject_Add` — plus a `./configure.sh` in the same spirit but
smaller. Phase 1 keeps the git submodules in the tree; Phase 2 considers
folding them in too.

This document is the design, not the implementation. Nothing here has been
built yet.

---

## 1. Where STP is today

Eight dependencies are fetched by hand-written shell scripts under
`scripts/deps/`, four are git submodules, two are vendored source, and the
rest come from the system.

### 1.1 Script-fetched (`scripts/deps/*.sh` → `deps/` in the **source** tree)

| Dependency | Pin | Built how | Consumed how |
|---|---|---|---|
| **LibBF** | `stp/libbf` @ `334e7aee` | `cc -O2 -fPIC -c` ×2, `ar rcs` | `LIBBF_DIR` (default `deps/libbf`) → `find_path`/`find_library`, then **global** `include_directories(SYSTEM)` + `link_libraries()`. Required. |
| **CaDiCaL** | `arminbiere/cadical` @ `rel-3.0.1`, overridable via `$CADICAL_TAG` | `./configure -fPIC && make` | `CADICAL_DIR` → `find_path(src/cadical.hpp)` + `find_library(... PATHS <dir>/build)`, both `NO_DEFAULT_PATH`; version read from the checkout's `VERSION` file; **global** `include_directories` + `link_libraries` |
| **CryptoMiniSat** | `msoos/cryptominisat` @ `release/v5.14.7` | CMake, static+PIC, installed to `deps/install` | `find_package(cryptominisat5 CONFIG)` via `CMAKE_PREFIX_PATH`; needs `find_package(cadical/cadiback CONFIG QUIET)` first |
| **MiniSat** | `stp/minisat` @ `14c78206` | CMake, static+PIC, installed to `deps/install` | `find_package(minisat)` then `find_package(minisat CONFIG)` |
| **Riss** | `conp-solutions/riss` @ `41342f15`, overridable via `$RISS_COMMIT` | CMake, static+PIC, **not** installed | `RISS_DIR` → `find_path`/`find_library` `NO_DEFAULT_PATH` |
| **GTest** | `google/googletest` @ `v1.17.0` | not built by the script | `add_subdirectory(deps/gtest)` from `tests/CMakeLists.txt` |
| **OutputCheck** | `stp/OutputCheck` — **unpinned** | n/a (Python) | path computed inside `tests/query-files/lit.cfg` from the source root |

### 1.2 Git submodules (`lib/extlib-*`)

| Submodule | Upstream | Consumed how |
|---|---|---|
| **ABC** | `stp/abc` (an STP fork) | `add_subdirectory(lib/extlib-abc EXCLUDE_FROM_ALL)` with `BUILD_SHARED_LIBS` shadowed OFF; links `$<TARGET_FILE:libabc-pic>`; per-target `-Wno-error` and `-ffunction-sections -fdata-sections`; global `include_directories(SYSTEM .../src)`; `LIN`/`LIN64`/`NT64` defines |
| **mimalloc** | `microsoft/mimalloc` | `add_subdirectory(lib/extlib-mimalloc EXCLUDE_FROM_ALL)` with five `MI_*` cache vars FORCEd; links `mimalloc-static`; the shared `mimalloc` target is un-excluded for `LD_PRELOAD` tests |
| **SymFPU** | `martin-cs/symfpu` | header-only; `include_directories(SYSTEM ${SYMFPU_INCLUDE_DIRS})`, where that is the *parent* of the clone (sources say `#include "symfpu/core/..."`). Four local patches in `patches/symfpu/` applied at configure time by `stp_apply_vendored_patches()` |
| **CLI11** | `CLIUtils/CLI11` | header-only; include added on the `stp-bin` target only |

### 1.3 Vendored source (no submodule, no fetch)

`lib/extlib-constbv` (STP's own) and `lib/extlib-unordered-dense`
(`ankerl::unordered_dense`, copied in). Neither is in scope.

### 1.4 System-found

Bison ≥ 2.6 (REQUIRED), Flex (REQUIRED), Python 3 (REQUIRED — it generates
`ASTKind.{h,cpp}`), `lit` (tests), zlib (only under `USE_MINISAT`), GMP
(only reached transitively through CryptoMiniSat's config file), tcmalloc
(optional allocator), help2man and valgrind (optional).

None of these should move. They are toolchain, not payload.

### 1.5 What is actually wrong with this

Not "it doesn't work" — it works. The specific costs:

1. **Nothing carries STP's toolchain into the dependency.** Each script
   hard-codes `cc`, `ar`, `nproc`, `-fPIC` and a build type. A cross-compile
   (`scripts/ci-32bit.sh`, the MinGW CaDiCaL job), a `CMAKE_TOOLCHAIN_FILE`,
   a compiler launcher (`ccache`/`sccache`), an `--sysroot`, or
   `-DSANITIZE=ON` reaches STP's own sources and stops at the dependency
   boundary.
2. **Five of the eight scripts are Linux-only.** `nproc` and `readlink -fm`
   are GNU coreutils; `setup-cms.sh`, `setup-minisat.sh`, `setup-riss.sh`,
   `setup-cadical.sh` and `setup-outputcheck.sh` use one or both.
   (`scripts/extdiff-baseline-differential.sh` has the
   `nproc || sysctl -n hw.ncpu` fallback — the dep scripts do not.)
3. **Windows needs a second, bespoke recipe per dependency.** The MSVC job
   runs `setup-libbf.sh` with `LIBBF_NO_BUILD=1` and then compiles LibBF with
   `cl`/`lib` in PowerShell; MiniSat is cloned and built inline in the job.
   None of that is shared with the Linux path.
4. **The pins live away from the consumption logic.** `rel-3.0.1` is in a
   shell script; the `>= 3.0.0 → -DSTP_CADICAL_HAS_FACTOR` decision that
   depends on it is in `CMakeLists.txt`, and derives the version from a
   `VERSION` file that only exists in a checkout — so a system CaDiCaL is
   `"unknown"` and silently loses `--cadical-factor`.
5. **`deps/` is in the source tree**, so it is shared by every build
   directory — convenient, but it also means a `git clean` destroys an hour
   of CryptoMiniSat, and it is why `deps/install` had to go on
   `CMAKE_PREFIX_PATH`, which is in turn why `CADICAL_DIR` and `RISS_DIR`
   need `PATHS ... NO_DEFAULT_PATH` to avoid being outranked by a bundled
   CaDiCaL that CryptoMiniSat installed there.
6. **A clean clone does not configure.** You need
   `git submodule update --init`, then `setup-libbf.sh`, then at least one
   backend script, then `cmake`. `Dockerfile` does none of these — it
   `.dockerignore`s `scripts/`, `.git` and `.gitmodules` entirely, so it only
   builds if the host tree already has populated submodules and a built
   `deps/libbf`.
7. **67 references** to `scripts/deps/setup-*.sh` and `cache-key.sh` across
   CI, docs and scripts, all of which encode the layout.

---

## 2. What cvc5 actually does

Three files carry the whole mechanism.

**`cmake/deps-helper.cmake`** sets `DEPS_PREFIX`/`DEPS_BASE` to
`${PROJECT_BINARY_DIR}/deps`, `file(MAKE_DIRECTORY "${DEPS_BASE}/include/")`
(CMake requires an `INTERFACE_SYSTEM_INCLUDE_DIRECTORIES` directory to exist
when the property is set, even though the headers arrive later), and defines
a shared `COMMON_EP_CONFIG` — `PREFIX`, `LOG_*`, `LOG_MERGED_STDOUTERR`,
`LOG_OUTPUT_ON_FAILURE`. It also defines the four macros every Find module
uses:

- `check_auto_download(name disable_option)` — `FATAL_ERROR` unless
  `ENABLE_AUTO_DOWNLOAD`, with a message naming both `--auto-download` and
  the flag that turns this dependency off.
- `check_ep_downloaded(name)` — true if `${DEPS_PREFIX}/src/${name}` exists,
  so a reconfigure of a tree that already downloaded a dependency does not
  demand `--auto-download` again.
- `check_system_version(name)` — compares `${name}_VERSION` against
  `${name}_FIND_VERSION` / `${name}_FIND_VERSION_MAX` and clears
  `${name}_FOUND_SYSTEM`.
- `force_static_library` / `reset_force_static_library`,
  `fail_if_cross_compiling`, `fail_if_include_missing`.

**`cmake/FindX.cmake`**, one per dependency, all the same shape:

```cmake
include(deps-helper)

find_path(X_INCLUDE_DIR NAMES x/x.h)
find_library(X_LIBRARIES NAMES x)

set(X_FOUND_SYSTEM FALSE)
if(X_INCLUDE_DIR AND X_LIBRARIES)
  # ... determine X_VERSION ...
  set(X_FOUND_SYSTEM TRUE)
  check_system_version("X")
endif()

if(NOT X_FOUND_SYSTEM)
  check_ep_downloaded("X-EP")
  if(NOT X-EP_DOWNLOADED)
    check_auto_download("X" "--no-x")
  endif()
  include(ExternalProject)
  set(X_VERSION "1.2.3")
  ExternalProject_Add(X-EP ${COMMON_EP_CONFIG}
    URL https://.../${X_VERSION}.tar.gz
    URL_HASH SHA256=...
    CMAKE_ARGS -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR> ...
    BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libx.a)
  set(X_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(X_LIBRARIES  "${DEPS_BASE}/lib/libx.a")
endif()

set(X_FOUND TRUE)
add_library(X STATIC IMPORTED GLOBAL)
set_target_properties(X PROPERTIES
  IMPORTED_LOCATION "${X_LIBRARIES}"
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${X_INCLUDE_DIR}")

if(X_FOUND_SYSTEM)
  message(STATUS "Found X ${X_VERSION}: ${X_LIBRARIES}")
else()
  message(STATUS "Building X ${X_VERSION}: ${X_LIBRARIES}")
  add_dependencies(X X-EP)
  if(NOT BUILD_SHARED_LIBS)
    install(FILES ${X_LIBRARIES} TYPE ${LIB_BUILD_TYPE})
  endif()
endif()
```

Four details in there are load-bearing and easy to miss:

- The **imported target is created either way**, so the rest of the build
  never branches on system-vs-built.
- `add_dependencies(X X-EP)` on an *imported* target is what orders the EP
  before anything that links `X`.
- `BUILD_BYPRODUCTS` is what makes Ninja accept a link input that does not
  exist at generate time. Omitting it works under Make and fails under Ninja
  — which is the generator every STP CI job uses.
- `install(FILES ${X_LIBRARIES} ...)` when static: a consumer of a static
  libstp has to resolve libstp's private dependencies itself, so the archive
  must ship.

**`configure.sh`** is a pure argument translator: `--foo` → `-DUSE_FOO=ON`,
`--no-foo` → `-DUSE_FOO=OFF`, positional build type → `-DCMAKE_BUILD_TYPE=`,
`-D*` passed through verbatim; then `mkdir -p $build_dir; cd $build_dir; rm
CMakeCache.txt; cmake "$root_dir" "${cmake_opts[@]}"`. Every option defaults
to the literal string `default` and is only emitted if it was set, which is
what lets `CMakeLists.txt` own the real defaults. That pairs with
`cvc5_option(VAR)` / `cvc5_set_option(VAR value)` — a three-valued
`IGNORE`/`ON`/`OFF` cache entry, so the build can tell "user said OFF" from
"user said nothing".

---

## 3. The structural mismatch: STP has three kinds of dependency, cvc5 has one

This is the single most important finding, and it is why a straight
transliteration of cvc5's `cmake/` into STP would be wrong.

Every one of cvc5's dependencies is consumed as **a header set plus a library
file**. Nothing in cvc5's own build reaches inside a dependency's targets.
That is why `ExternalProject_Add` — which builds in a *separate CMake
invocation*, at *build* time, with *no target visibility* — is a perfect fit
for all of them.

STP's dependencies fall into three classes:

### Class A — binary dependencies

**LibBF, CaDiCaL, CryptoMiniSat, MiniSat, Riss** (and transitively zlib, GMP).

Headers plus an archive. Nothing of STP's build reaches inside.
→ **`ExternalProject_Add` + imported target. cvc5's model applies verbatim.**

### Class B — source dependencies

**ABC, mimalloc, GTest.**

These must be *CMake targets inside STP's build*, because STP:

- forces `BUILD_SHARED_LIBS OFF` around ABC and links
  `$<TARGET_FILE:libabc-pic>`;
- applies `target_compile_options(... -Wno-error)` and
  `-ffunction-sections -fdata-sections` to ABC's targets specifically, so
  `--gc-sections` can drop what STP never calls;
- FORCEs five `MI_*` cache variables into mimalloc and then re-includes its
  shared target for the `LD_PRELOAD` tests
  (`tests/api/python/allocator_tests.py`);
- deliberately compiles GTest with STP's own flags — the comment in
  `tests/CMakeLists.txt` says so in as many words — plus
  `gtest_force_shared_crt` on MSVC;
- expects all three to inherit `SANITIZE`'s `CMAKE_CXX_FLAGS` and the UBSan
  CI job's instrumentation. That job exists specifically to cover *the
  vendored C*.

**Correction (asked, and checked, after the work was done): this was
overstated.** `ExternalProject_Add` *can* express nearly all of it. `CMAKE_ARGS`
forwards any cache variable or flag — which is what `STP_EP_COMMON_CMAKE_ARGS`
already does for the compiler, flags, launcher, sysroot and PIC; ABC's two
environment variables would go through `${CMAKE_COMMAND} -E env`; building one
target is `BUILD_COMMAND --target`; and `$<TARGET_FILE:libabc-pic>` becomes a
path, which `lib/CMakeLists.txt` already prefers for export reasons. cvc5's own
`FindGTest.cmake` builds GoogleTest exactly this way.

So the real distinction is not possibility, it is **granularity against
payoff**:

- *Lost:* per-target precision. `-Wno-error` and `-ffunction-sections` land on
  ABC's targets specifically today; forwarded, they apply to the whole
  sub-build. For ABC that is the same set of files, so nothing real is lost —
  but it is a coarser instrument.
- *Gained, and underweighted first time round:* the artefact installs into the
  shared `STP_DEP_DIR` and is **built once across build directories**. ABC is
  920 C files and is currently recompiled in every one. For anyone running
  several build directories that is likely the largest build-time saving
  available anywhere in this exercise.
- *Risked:* ABC's compile-time flags must agree with STP's own, because STP's
  sources include ABC's headers — `-DLIN64`/`-DNT64`, `ABC_USE_NO_PTHREADS`,
  and anything else that changes a declaration in `aig.h`, `dar.h` or `cnf.h`.
  A shared ABC built by a differently-configured STP would be silently wrong,
  and `.stp-dep-config` does not record those defines.

The one where the arithmetic clearly favours ExternalProject is **ABC**, on
build time. **Done (7bcde9b3).** The stamp was extended first, as this said it
needed to be: `ABC_ABI_DEFINITIONS` is collected in one place, forwarded to
ABC's build, and recorded in `.stp-dep-config`, so a shared ABC built for
another pointer width is a warning rather than a crash in CNF generation. The
build type is still deliberately excluded — sharing an ABC at another
optimisation level is a choice; sharing one at another pointer width is not.

Two things that had to be dealt with, neither anticipated here:

- **ABC's headers reach most of the tree.** `stp/ToSat/BBNodeAIG.h` includes
  `aig/aig/aig.h`, so every object library links the ABC target — which
  supplies the include directory *and* the ordering that a project-wide
  `include_directories()` could not express. Same shape as SymFPU and
  `unordered_dense`; the third time this pattern came up.
- **ABC has no install rules at all** — two `EXCLUDE_FROM_ALL` libraries and
  nothing else — so it needs a copy step of its own, like MiniSat and Riss.

Measured, Release, same machine: `libstp.so` 6.6 MB before, 6.7 MB after, so
`--exclude-libs` and `--gc-sections` still work. (The "~3.4MB" in the comment
above that link flag is stale, and was stale before this.)

GoogleTest and mimalloc are small and quick to build, so converting them would
be for consistency rather than gain.

What remains genuinely impossible is narrower than this section first claimed:
only that an ExternalProject cannot make a source tree exist *during the
configure that needs it*. That is what rules it out for a project-wide include
with no target to order against — `ankerl::unordered_dense` — and it is why
FetchContent, not ExternalProject, is the tool for anything STP must
`add_subdirectory`.

→ **These stay `add_subdirectory`.** If the *source* should be fetched
rather than submoduled, the tool is **`FetchContent`**, which downloads at
*configure* time so that `add_subdirectory` has something to descend into.
cvc5 has no dependency in this class, which is why its `cmake/` contains no
`FetchContent` at all.

### Class C — header-only dependencies

**SymFPU, CLI11** (and `unordered-dense`, already vendored outright).

Only an include directory is needed. Either mechanism works.
→ **`ExternalProject_Add` with `CONFIGURE_COMMAND ""`/`BUILD_COMMAND ""` and
a copy-based `INSTALL_COMMAND`**, exactly as cvc5's `FindSymFPU.cmake` does.
For SymFPU this additionally gets the four local patches handled by
`PATCH_COMMAND` for free.

**The rule this yields:** *`ExternalProject` for what STP links;
`FetchContent` (or a submodule) for what STP compiles.*

---

## 4. Target architecture

### 4.1 Layout

```
cmake/
  deps-helper.cmake            # DEPS_BASE, COMMON_EP_CONFIG, the macros
  deps-utils/
    libbf-CMakeLists.txt       # injected build system for LibBF
    symfpu/000{1..4}-*.patch   # moved from patches/symfpu/ in Phase 2
  FindLibBF.cmake
  FindCaDiCaL.cmake
  FindCryptoMiniSat.cmake
  FindMiniSat.cmake            # replaces cmake/modules/Findminisat.cmake
  FindRiss.cmake
  FindSymFPU.cmake             # rewritten; the current one is a 20-line stub
  FindCLI11.cmake              # Phase 2
  modules/                     # unchanged: AddGTestSuite, AddSTPGTest,
                               # GetGitRevisionDescription, cmake_uninstall
configure.sh
```

`CMAKE_MODULE_PATH` currently is *only* `${PROJECT_SOURCE_DIR}/cmake/modules`
(a `set`, not an `APPEND`). It becomes
`${PROJECT_SOURCE_DIR}/cmake;${PROJECT_SOURCE_DIR}/cmake/modules`.

### 4.2 Where the dependency tree lives: `--dep-dir`

cvc5 puts everything under `${PROJECT_BINARY_DIR}/deps` and offers
`--dep-path=PATH`, which only *appends to* `CMAKE_PREFIX_PATH` — read-only.
STP wants more: one directory a run can both **inherit from** and **install
into**, so that N build directories against one source tree pay for
CryptoMiniSat once.

What makes that safe is splitting the two trees cvc5 conflates.
`ExternalProject` has:

| Tree | Contents | Shareable? |
|---|---|---|
| `PREFIX` | `src/`, `tmp/`, `stamp/`, `<name>-build/` | **No.** Stamp files are per-configuration mutable state; two builds sharing them corrupt each other. |
| `INSTALL_DIR` | `include/`, `lib/`, `bin/` | **Yes.** Write-once, read-many, content fully determined by the pin. |

So:

- **`STP_DEP_DIR`** (cache PATH; `--dep-dir=PATH`) names the *install* tree.
  It becomes every EP's `INSTALL_DIR` **and** goes on the front of
  `CMAKE_PREFIX_PATH`.
- The EP `PREFIX` stays at `${PROJECT_BINARY_DIR}/deps`, always. Per build
  directory, so stamp races cannot happen.

Inherit-vs-install then falls straight out of the ladder in §4.3, with no
extra machinery:

- **First build directory:** rung 1 finds nothing → rung 3 creates the EP →
  it installs into `${STP_DEP_DIR}`.
- **Every later build directory:** rung 1 finds
  `${STP_DEP_DIR}/lib/libcadical.a` and `${STP_DEP_DIR}/include/…` →
  `CaDiCaL_FOUND_SYSTEM=TRUE` → **no ExternalProject is created at all.** No
  stamp directory, no rebuild, and no `--auto-download` needed.

That last point is worth stating plainly: with `--dep-dir` set, only the
*first* configure touches the network. Later ones are pure lookups.

**Default.** `STP_DEP_DIR` unset ⇒ `${PROJECT_BINARY_DIR}/deps` — cvc5's
behaviour: self-contained, per-build, `rm -rf build` really removes
everything. The source tree's `deps/install` **stays on
`CMAKE_PREFIX_PATH`** as a read-only legacy rung, so existing checkouts and
any lingering `scripts/deps/*.sh` output keep being found with no flags
during the transition.

**Environment default.** `configure.sh` honours `$STP_DEP_DIR`, so
`export STP_DEP_DIR=~/.cache/stp/deps` in a shell profile makes sharing the
default for one developer without editing any script. Precedence:
`--dep-dir=` > `$STP_DEP_DIR` > per-build default. Only `configure.sh` reads
the environment — the CMake cache variable stays the single source of truth
for the build itself.

**The one real hazard: a shared dep directory is not keyed by
configuration.** An ASan build and a plain Release build pointed at one
`--dep-dir` will fight over the same `libcadical.a`, and the resulting link
error or sanitizer runtime mismatch will not obviously point back here.

Mitigation: have `deps-helper.cmake` write
`${STP_DEP_DIR}/.stp-dep-config` recording the facts that actually change the
artefacts —

```
compiler=GNU 14.2.0
build_type=Release
pic=ON
sanitize=OFF
toolchain=
```

— and on reuse compare it and `message(WARNING)` naming the fields that
differ. A warning, not an error: "one dep directory, several build types" is
exactly the case `--dep-dir` exists to serve, and a `Release` /
`RelWithDebInfo` mismatch is harmless. `sanitize` and `compiler` are the ones
worth shouting about.

**Residual race.** Two *concurrent first* configures against one
`--dep-dir` will both build and both install. Same pin, so the content is
identical; the window in which a reader could see a half-written archive is
small, and the failure is a link error rather than a wrong answer. The clean
answer is to warm the directory once — see §5.6.

### 4.3 The lookup ladder — STP needs one more rung than cvc5

cvc5's ladder is: system → already-downloaded → auto-download → fatal.

STP has explicit per-dependency directory variables that CI, the docs and
local campaign scripts all set: `CADICAL_DIR`, `RISS_DIR`, `LIBBF_DIR`,
`SYMFPU_INCLUDE_DIRS`, `cryptominisat5_DIR`, `MINISAT_INCLUDE_DIRS` /
`MINISAT_LIBDIR`. These must keep working, and they must **outrank
everything**.

They already do, and the reason is written up at length in `CMakeLists.txt`
over the `USE_CADICAL` block: `find_library` reaches `CMAKE_PREFIX_PATH`
*before* `HINTS`, and `deps/install` is on that path, so a
`HINTS`-based lookup resolved `CADICAL_DIR` to CryptoMiniSat's *bundled*
CaDiCaL instead. The fix was `PATHS ... NO_DEFAULT_PATH`. **That discipline
must survive the migration**, and the EP rung makes it strictly more
important, because there is now a third CaDiCaL in play.

So the STP ladder is:

```
0. <X>_DIR explicitly set     → use it, or FATAL_ERROR. Never fall through.
1. system / CMAKE_PREFIX_PATH → find_path/find_library/find_package CONFIG
                                (this rung covers legacy deps/install)
2. EP already downloaded      → check_ep_downloaded
3. ENABLE_AUTO_DOWNLOAD       → ExternalProject_Add
4. FATAL_ERROR naming both --auto-download and -D<X>_DIR=
```

Rung 0 failing loudly rather than falling through is the behaviour STP
already has (`"USE_CADICAL is set but CaDiCaL was not found"`) and is worth
keeping: silently downloading a different CaDiCaL than the one the user
named would be a worse bug than the one the `NO_DEFAULT_PATH` comment
describes.

### 4.4 Worked example: `cmake/FindLibBF.cmake`

LibBF is the best first target — required, script-fetched, has no build
system of its own, and currently needs a separate MSVC recipe in CI.

The trick is to inject a build system. `cmake/deps-utils/libbf-CMakeLists.txt`:

```cmake
cmake_minimum_required(VERSION 3.18)
project(libbf C)
add_library(bf STATIC libbf.c cutils.c)
set_target_properties(bf PROPERTIES POSITION_INDEPENDENT_CODE ON)
install(TARGETS bf ARCHIVE DESTINATION lib)
install(FILES libbf.h cutils.h DESTINATION include)
```

and `cmake/FindLibBF.cmake`:

```cmake
include(deps-helper)

# Rung 0: LIBBF_DIR names a build, as scripts/deps/setup-libbf.sh produced.
if(LIBBF_DIR)
  find_path(LibBF_INCLUDE_DIR NAMES libbf.h PATHS ${LIBBF_DIR} NO_DEFAULT_PATH)
  find_library(LibBF_LIBRARIES NAMES bf     PATHS ${LIBBF_DIR} NO_DEFAULT_PATH)
  if(NOT LibBF_INCLUDE_DIR OR NOT LibBF_LIBRARIES)
    message(FATAL_ERROR "LIBBF_DIR is set to '${LIBBF_DIR}' but it does not "
            "contain libbf.h and a bf library.")
  endif()
  set(LibBF_FOUND_SYSTEM TRUE)
else()
  find_path(LibBF_INCLUDE_DIR NAMES libbf.h)
  find_library(LibBF_LIBRARIES NAMES bf)
  set(LibBF_FOUND_SYSTEM FALSE)
  if(LibBF_INCLUDE_DIR AND LibBF_LIBRARIES)
    set(LibBF_FOUND_SYSTEM TRUE)
  endif()
endif()

if(NOT LibBF_FOUND_SYSTEM)
  check_ep_downloaded("LibBF-EP")
  if(NOT LibBF-EP_DOWNLOADED)
    check_auto_download("LibBF" "")      # "" == not optional
  endif()
  include(ExternalProject)

  # Upstream publishes tarballs on bellard.org and no repository, so STP
  # mirrors them: master holds the releases verbatim, the stp branch adds
  # the MSVC portability shims. A commit, not a tag -- that branch is
  # rebased onto each import.
  set(LibBF_VERSION "334e7aeec2b0b2be7768285f279b99d1368c5fa9")

  ExternalProject_Add(LibBF-EP
    ${COMMON_EP_CONFIG}
    GIT_REPOSITORY https://github.com/stp/libbf
    GIT_TAG        ${LibBF_VERSION}
    GIT_SHALLOW    FALSE
    # The mirror carries tests, benchmarks and the calculator demo; none of
    # it is wanted, and there is no build system. Supply one.
    PATCH_COMMAND ${CMAKE_COMMAND} -E copy
                  ${CMAKE_CURRENT_LIST_DIR}/deps-utils/libbf-CMakeLists.txt
                  <SOURCE_DIR>/CMakeLists.txt
    CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS}
               -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
    BUILD_BYPRODUCTS
      <INSTALL_DIR>/lib/${CMAKE_STATIC_LIBRARY_PREFIX}bf${CMAKE_STATIC_LIBRARY_SUFFIX}
  )

  set(LibBF_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(LibBF_LIBRARIES
      "${DEPS_BASE}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}bf${CMAKE_STATIC_LIBRARY_SUFFIX}")
endif()

set(LibBF_FOUND TRUE)

add_library(LibBF UNKNOWN IMPORTED GLOBAL)
set_target_properties(LibBF PROPERTIES
  IMPORTED_LOCATION "${LibBF_LIBRARIES}"
  # BOTH include properties -- see the note below.
  INTERFACE_INCLUDE_DIRECTORIES "${LibBF_INCLUDE_DIR}"
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${LibBF_INCLUDE_DIR}")

if(LibBF_FOUND_SYSTEM)
  message(STATUS "Found LibBF: ${LibBF_LIBRARIES}")
else()
  message(STATUS "Building LibBF ${LibBF_VERSION}: ${LibBF_LIBRARIES}")
  add_dependencies(LibBF LibBF-EP)
  if(NOT BUILD_SHARED_LIBS)
    install(FILES ${LibBF_LIBRARIES} TYPE ${LIB_BUILD_TYPE})
  endif()
endif()
```

What this buys, concretely: **the MSVC-specific LibBF steps in
`.github/workflows/ci.yml` disappear** — `cl`, `lib /OUT:bf.lib` and the
`LIBBF_NO_BUILD=1` escape hatch in the script all become one CMake sub-build
that works with cl, gcc, clang, MinGW and emcc identically. `-fPIC`,
`ccache`, the sysroot and the toolchain file arrive via
`STP_EP_COMMON_CMAKE_ARGS`.

`GIT_REPOSITORY`/`GIT_TAG` rather than cvc5's `URL`/`URL_HASH` is deliberate
here — see §8.3.

**Two include properties, not one — a correction to cvc5's recipe.** cvc5's
Find modules set only `INTERFACE_SYSTEM_INCLUDE_DIRECTORIES` on the imported
target. That property does not *add* an include directory; it only says that a
directory already on the compile line should be spelled `-isystem`. cvc5 gets
away with it because `src/CMakeLists.txt` separately calls

```cmake
target_include_directories(cvc5-obj SYSTEM PRIVATE ${CaDiCaL_INCLUDE_DIR})
```

for every single dependency — so the imported target carries the library and a
hand-written line carries the header.

STP should set **both** `INTERFACE_INCLUDE_DIRECTORIES` and
`INTERFACE_SYSTEM_INCLUDE_DIRECTORIES`, so that one
`target_link_libraries(<consumer> PRIVATE LibBF)` delivers the header *and* the
archive together. Beyond being less to write, it removes the failure mode STP
has already been bitten by once: the long `NO_DEFAULT_PATH` note over the
`USE_CADICAL` block exists because STP compiled against the headers
`CADICAL_DIR` named and linked a different CaDiCaL's library. A target that
carries both cannot be made to disagree with itself.

(Setting only the SYSTEM property fails silently — nothing warns, the directory
simply never appears, and the first `#include` of the dependency is a fatal
error a long way from the cause.)

### 4.5 `STP_EP_COMMON_CMAKE_ARGS` — an improvement on cvc5

cvc5 forwards `CMAKE_TOOLCHAIN_FILE` and little else, and repeats
`CMAKE_OSX_SYSROOT` handling per file. STP should define one list in
`deps-helper.cmake` and use it in every CMake-based EP:

```cmake
set(STP_EP_COMMON_CMAKE_ARGS
    -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE}
    -DCMAKE_C_COMPILER=${CMAKE_C_COMPILER}
    -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}
    -DCMAKE_C_FLAGS=${CMAKE_C_FLAGS}
    -DCMAKE_CXX_FLAGS=${CMAKE_CXX_FLAGS}
    -DCMAKE_C_COMPILER_LAUNCHER=${CMAKE_C_COMPILER_LAUNCHER}
    -DCMAKE_CXX_COMPILER_LAUNCHER=${CMAKE_CXX_COMPILER_LAUNCHER}
    -DCMAKE_POSITION_INDEPENDENT_CODE=ON
    -DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}
    -DCMAKE_OSX_SYSROOT=${CMAKE_OSX_SYSROOT}
    -DCMAKE_OSX_ARCHITECTURES=${CMAKE_OSX_ARCHITECTURES}
    -DCMAKE_EXPORT_NO_PACKAGE_REGISTRY=ON
    -DCMAKE_POLICY_VERSION_MINIMUM=3.12)
```

Four of these fix things that are broken or hand-patched today:

- `CMAKE_*_COMPILER_LAUNCHER` — CI's ccache/sccache currently stops at the
  STP boundary; CryptoMiniSat, the most expensive dependency in CI, is never
  cached by it (only by `actions/cache` on `deps/install`).
- `CMAKE_POSITION_INDEPENDENT_CODE` — hand-set in three separate scripts,
  each with its own comment explaining why.
- `CMAKE_POLICY_VERSION_MINIMUM=3.12` — hand-set in `setup-minisat.sh`
  (3.12) and `setup-riss.sh` (3.5) because those projects predate CMake 4's
  floor.
- `CMAKE_C_FLAGS`/`CMAKE_CXX_FLAGS` — carries `SANITIZE`'s
  `-fsanitize=address` into the dependency, without which an ASan build of
  STP against a non-ASan CryptoMiniSat is a link error waiting to happen.

`PIC ON` unconditionally is correct for STP: every static dependency is
linked into `libstp.so`.

### 4.6 Imported targets, and the global `link_libraries()` problem

Two dependencies are wired in globally today:

```cmake
include_directories(${CADICAL_INCLUDE_DIR})     # every target in the project
link_libraries(${CADICAL_LIBRARY})
include_directories(SYSTEM ${LIBBF_INCLUDE_DIR})
link_libraries(${LIBBF_LIBRARY})
```

This has to go, for two reasons. First, `link_libraries(<absolute path>)`
gives nothing to hang `add_dependencies` on, so a `ninja` build would try to
link an archive the EP has not produced yet. Second, both are far wider than
needed: LibBF is used by exactly one translation unit
(`lib/FloatBlaster/DecimalLiteral.cpp`), CaDiCaL by `lib/Sat/Cadical.cpp` and
`lib/Sat/SATSolverFactory.cpp`.

Replacement:

```cmake
target_link_libraries(FloatBlaster PRIVATE LibBF)   # in lib/FloatBlaster/
target_link_libraries(Sat          PRIVATE CaDiCaL) # in lib/Sat/
```

This is a **prerequisite**, not a nice-to-have, and it is the largest
non-mechanical part of the work. It also has to be checked against the object
libraries: `lib/CMakeLists.txt` assembles `stp` from a list of object
libraries, and `target_link_libraries` on an `OBJECT` library propagates
usage requirements but not the archive, so the final link may need the
imported target named on `stp` as well.

### 4.7 Export and install

`STPTargets.cmake` is generated by `export(TARGETS stp)` and
`install(EXPORT ...)`. If `stp` links imported targets named `CaDiCaL`,
`LibBF` etc., those names appear in the generated file and a consumer's
`find_package(STP)` will fail on them.

`lib/CMakeLists.txt` already dodges this for ABC — it links
`$<TARGET_FILE:libabc-pic>`, a path rather than a target name, with a comment
saying "for export compatibility". Three options, in order of preference:

1. Link the imported targets `PRIVATE` **and** build `libstp` shared. A
   shared library resolves its own private dependencies, so nothing leaks.
   This is already the default (`BUILD_SHARED_LIBS=ON`).
2. For static builds, follow cvc5: `install(FILES ${X_LIBRARIES} TYPE
   ${LIB_BUILD_TYPE})` when `NOT BUILD_SHARED_LIBS`, and have
   `STPConfig.cmake.in` re-create the imported targets — it already does
   something in this spirit for CryptoMiniSat (`find_package(cadical CONFIG
   QUIET)` before `find_dependency(cryptominisat5)`).
3. Wrap in `$<BUILD_INTERFACE:...>` and re-find at consume time.

**Static builds are the case to test first.** `STATICCOMPILE=ON` is what the
release job, the Docker image and the Windows job all use, and it is the
configuration where this breaks.

---

## 5. `configure.sh`

Barebones: an argument translator, ~200 lines, no logic of its own. STP's
`CMakeLists.txt` keeps owning every default.

### 5.1 Option surface

| Positional | Effect |
|---|---|
| `debug` | `-DCMAKE_BUILD_TYPE=Debug -DENABLE_ASSERTIONS=ON` |
| `release` | `-DCMAKE_BUILD_TYPE=Release` (assertions off — see §5.3) |
| `relwithdebinfo` | `-DCMAKE_BUILD_TYPE=RelWithDebInfo` (STP's current default) |
| `minsizerel` | `-DCMAKE_BUILD_TYPE=MinSizeRel` |

| Flag | CMake |
|---|---|
| `--prefix=P` | `-DCMAKE_INSTALL_PREFIX=P` |
| `--name=N` | build directory (default `build`) |
| `--ninja` | `-G Ninja` |
| `--auto-download` | `-DENABLE_AUTO_DOWNLOAD=ON` |
| `--dep-dir=P` | `-DSTP_DEP_DIR=P` — inherit from *and* install into P (§4.2); also honours `$STP_DEP_DIR` |
| `--dep-path=P` | appends to `-DCMAKE_PREFIX_PATH` — read-only, for a prefix STP must not write to |
| `--static` | `-DSTATICCOMPILE=ON` |
| `--assertions` / `--no-assertions` | `-DENABLE_ASSERTIONS=` |
| `--testing` / `--no-testing` | `-DENABLE_TESTING=` |
| `--werror` | `-DWERROR=ON` |
| `--sanitize` | `-DSANITIZE=ON` |
| `--coverage` | `-DCOVERAGE=ON` |
| `--python-bindings` / `--no-…` | `-DENABLE_PYTHON_INTERFACE=` |
| `--cadical` / `--no-cadical` | `-DUSE_CADICAL=` |
| `--cadical-dir=P` | `-DCADICAL_DIR=P` (implies `--cadical`) |
| `--cryptominisat` / `--no-cryptominisat` | `-DUSE_CRYPTOMINISAT=` |
| `--minisat` / `--no-minisat` | `-DUSE_MINISAT=` |
| `--riss` / `--no-riss` | `-DUSE_RISS=` |
| `--riss-dir=P` | `-DRISS_DIR=P` (implies `--riss`) |
| `--allocator=X` | `-DSTP_ALLOCATOR=X` |
| `--tune-native` | `-DTUNE_NATIVE=ON` |
| `-D...` | passed through verbatim |
| `-h`, `--help` | usage |

Everything defaults to the string `default` and is emitted only if set —
cvc5's pattern exactly.

### 5.2 Trap: the `NOCRYPTOMINISAT` polarity

STP's option is negative (`NOCRYPTOMINISAT`), and `USE_CRYPTOMINISAT` is
currently a *derived variable* the CMakeLists `set()`s when the package is
found. `configure.sh` should present `--cryptominisat` / `--no-cryptominisat`
and the CMakeLists should grow a real `USE_CRYPTOMINISAT` option, with
`NOCRYPTOMINISAT` kept as a deprecated alias.

There is a precedent to copy verbatim: the `USE_TCMALLOC` →
`STP_ALLOCATOR` back-compat block already in `CMakeLists.txt`, which warns
and FORCEs the new variable once.

### 5.3 Trap: `ENABLE_ASSERTIONS` is silently overridden by `Release`

```cmake
option(ENABLE_ASSERTIONS "Build with assertions enabled" ON)
if(CMAKE_BUILD_TYPE STREQUAL "Release")
    set(ENABLE_ASSERTIONS OFF)
endif()
```

`-DENABLE_ASSERTIONS=ON -DCMAKE_BUILD_TYPE=Release` silently gives you a
build without assertions. `./configure.sh release --assertions` would inherit
that surprise.

This is exactly what cvc5's three-valued `cvc5_option`/`cvc5_set_option` is
for: make `ENABLE_ASSERTIONS` default to `IGNORE`, have the `Release` branch
`stp_set_option(ENABLE_ASSERTIONS OFF)` — which only applies if the user said
nothing — and honour an explicit `ON`. Small change, and it belongs with this
work because `configure.sh` is what makes the current behaviour visible.

### 5.4 Trap: `SANITIZE` FORCEs the compiler

`-DSANITIZE=ON` does `set(CMAKE_CXX_COMPILER "clang++" CACHE FILEPATH ""
FORCE)`, and sets no C compiler. Under `STP_EP_COMMON_CMAKE_ARGS` that means
a sanitized STP would forward `clang++` for C++ and whatever
`CMAKE_C_COMPILER` happens to be for C — potentially a mismatched pair — into
every dependency. Either set both, or have `configure.sh --sanitize` export
`CC=clang CXX=clang++` and let the normal detection run.

### 5.5 What `configure.sh` should *not* do

No `--best`, no cross-compilation toolchains (STP's 32-bit and MinGW paths
are CI scripts with their own logic), no WASM, no docs targets. Those are
cvc5 features that answer cvc5 problems.

### 5.6 A `deps` target, to warm a shared `--dep-dir`

cvc5 has no equivalent, and `--dep-dir` wants one:

```cmake
add_custom_target(deps)          # always exists, possibly empty
# ... and in each FindX.cmake, on the EP rung only:
#     add_dependencies(deps X-EP)
```

so that

```bash
./configure.sh --dep-dir=~/.cache/stp/deps --auto-download \
               --cadical --cryptominisat --name=build-warmup
cmake --build build-warmup --target deps
```

builds and installs every dependency and nothing else. Every later configure
against that `--dep-dir` resolves at rung 1, needs no network, and cannot
race. It is also the shape CI wants: one step populates the directory, every
job inherits it.

The target must exist **unconditionally** — including when every dependency
was found at rung 1 and no EP was created at all — or scripts calling it
break the moment the cache is warm.

---

## 6. Per-dependency plan, and the opt-in sweep

### LibBF — Class A, required
Fully described in §4.4. Highest value, lowest risk, no consumer-visible
change beyond the include becoming `INTERFACE_SYSTEM_INCLUDE_DIRECTORIES` on
a target. **Do this one first.**

### CaDiCaL — Class A. Two prerequisites.

**(a) The include spelling is checkout-relative.**
`include/stp/Sat/Cadical.h` has `#include "src/cadical.hpp"`. That is
CaDiCaL's *source tree* layout; no installation anywhere has a `src/`
directory. It is why `CADICAL_DIR` must name a checkout, and it means STP
cannot consume a system or EP-installed CaDiCaL at all.

Fix: adopt cvc5's spelling, `#include <cadical/cadical.hpp>`, have the EP
install to `<INSTALL_DIR>/include/cadical/cadical.hpp`, and for the
`CADICAL_DIR`-names-a-checkout case stage the header into
`${DEPS_BASE}/include/cadical/` with `configure_file(... COPYONLY)` so every
rung of the ladder presents the same layout downstream.

`stp/Sat/Cadical.h` is **not** an installed public header — `lib/CMakeLists.txt`
installs only `c_interface.h`, `fp.hpp` and `uf.hpp` — so this is an
internal change with no API consequence.

**(b) The version probe only works on a checkout.**
`file(READ "${CADICAL_INCLUDE_DIR}/VERSION")` gates
`STP_CADICAL_HAS_FACTOR`, `CADICAL_HAS_FACTOR` and `CADICAL_HAS_INPROBING`.
Replace with cvc5's `try_run` on `CaDiCaL::Solver::version()` for the system
rung, and a literal `set(CaDiCaL_VERSION ...)` for the EP rung. This fixes a
live defect: a system CaDiCaL is `"unknown"` today and silently loses
`--cadical-factor`.

**EP recipe.** CaDiCaL has no CMake. cvc5's `FindCaDiCaL.cmake` sidesteps its
`configure` script by copying `makefile.in` and `sed`-substituting `@CXX@`,
`@CXXFLAGS@`, `@ROOT@`, `@CONTRIB@` — which is what makes it work under
cross-compilation, and which is also why cvc5 needs `find_program(SHELL sh
REQUIRED)` on Windows. STP can lift that file nearly verbatim; it is the
single most complex Find module in the set. Note STP pins `rel-3.0.1` while
cvc5 pins `rel-2.1.3-elevate`, and STP's `>= 3.0.0` factor gate depends on
that — do not inherit cvc5's pin along with its recipe.

**Interaction to preserve.** The static-CryptoMiniSat + CaDiCaL guard in
`CMakeLists.txt` (both put a CaDiCaL on libstp's link line and their symbols
collide; the discriminator is `get_target_property(_cms_type cryptominisat5
TYPE)`) still applies, and matters *more* once STP can build its own CaDiCaL.

### CryptoMiniSat — Class A, `find_package` CONFIG
Nearly a copy of cvc5's `FindCryptoMiniSat.cmake`. Differences to keep:
- STP pins `release/v5.14.7`; cvc5 pins `5.11.21`. 5.14+ bundles its own
  CaDiCaL, which is the whole reason the collision guard exists. Keep STP's
  pin, keep the `find_package(cadical/cadiback CONFIG QUIET)` preamble in
  both `CMakeLists.txt` and `STPConfig.cmake.in`.
- The EP must default to **`-DBUILD_SHARED_LIBS=ON`** when `USE_CADICAL` is
  also on, otherwise STP's own guard rejects the configuration it just built.
  cvc5 does not face this because it never builds two CaDiCaLs.
- Keep `-DCMAKE_BUILD_TYPE=Release` (not `RelWithDebInfo`): the existing
  script's comment records that debug info was two thirds of the static
  binary, 76 MB against 24 MB.
- Keep the "say what is about to be asked, and of whom, before asking"
  `message(STATUS)` about GMP — `cryptominisat5Config.cmake` raises a
  `FATAL_ERROR` from inside itself when `gmp.pc` is missing, and nothing STP
  does can turn that into "not found".

### MiniSat — Class A
`cmake/modules/Findminisat.cmake` becomes `cmake/FindMiniSat.cmake` with the
ladder. Straightforward: `stp/minisat` is a CMake project with an install
rule. `MINISAT_INCLUDE_DIRS`/`MINISAT_LIBDIR` are documented and used by the
Windows CI job, so they become rung 0. zlib stays system-found (its headers
are in MiniSat's public headers) — do **not** EP zlib.

### Riss — Class A
Same shape, but Riss builds no install rule today, so the EP needs
`INSTALL_COMMAND` copies of `riss/` headers and
`build/lib/libriss-coprocessor.a`, or `--target
riss-coprocessor-lib-static` plus manual copies. Keep the
`-DCMAKE_CXX_FLAGS="-w -std=gnu++14"` and
`-DCMAKE_POLICY_VERSION_MINIMUM=3.5` from the current script — Riss does not
compile warning-free or as C++17. Note that passing `CMAKE_CXX_FLAGS` here
*conflicts* with `STP_EP_COMMON_CMAKE_ARGS`; Riss needs an override, which is
a good argument for `STP_EP_COMMON_CMAKE_ARGS` being a starting list that
per-dependency modules can amend rather than a sealed one.

### GTest — Class B: `FetchContent`, not `ExternalProject`
`tests/CMakeLists.txt` does `add_subdirectory(deps/gtest)` deliberately, so
GTest gets STP's flags, `gtest_force_shared_crt` on MSVC, and the sanitizer
instrumentation. Converting it to a cvc5-style EP (which yields
`GTest::GTest` / `GTest::Main` imported targets built with their own flags)
would break all three.

Instead: `FetchContent_Declare(googletest GIT_REPOSITORY ... GIT_TAG
v1.17.0)` + `FetchContent_MakeAvailable`, guarded by `ENABLE_TESTING`. The
existing `BUILD_GMOCK OFF`, `INSTALL_GTEST OFF`, `-Wno-error` and
`include_directories(SYSTEM ...)` handling all carries over unchanged.

Caveat: `FetchContent` downloads at *configure* time and has no
`ENABLE_AUTO_DOWNLOAD` gate of its own — gate it by hand, and honour
`FETCHCONTENT_SOURCE_DIR_GOOGLETEST` for offline builds.

### OutputCheck — test-only, Python
`FetchContent_Declare` + populate (it has no `CMakeLists.txt`, so
`MakeAvailable` will not try to `add_subdirectory` it). The path is currently
computed inside `tests/query-files/lit.cfg` from the source root; it must be
passed in through `lit.site.cfg` instead. **Pin it** — it is the one
dependency with no pin at all today, which is precisely why
`scripts/deps/cache-key.sh` has to `git ls-remote` it. Pinning it makes
`cache-key.sh` a pure hash of `cmake/Find*.cmake` and deletes its network
call.

### SymFPU — Class C. Phase 2.
Header-only, so cvc5's `FindSymFPU.cmake` is a near-exact fit. Two STP
specifics:

- **Include spelling.** STP says `#include "symfpu/core/add.h"`, so the
  include directory must be the *parent* of the clone. cvc5 installs to
  `<INSTALL_DIR>/include/symfpu/core/` and adds `<INSTALL_DIR>/include/` —
  the same spelling works. `SYMFPU_INCLUDE_DIRS` (documented, points at the
  directory *containing* the clone) becomes rung 0 unchanged.
- **The four local patches** move from `patches/symfpu/` to
  `cmake/deps-utils/` and are applied by `PATCH_COMMAND patch -p1 -d
  <SOURCE_DIR> -i ...`. They are `git diff` output with `a/`…`b/` prefixes,
  which `patch -p1` accepts, so no reformatting is needed.

  This **deletes `stp_apply_vendored_patches()`** — 60 lines of
  configure-time reverse-apply-check idempotency logic that exists only
  because the patches are applied to a submodule working tree that persists
  across configures. An EP patches once, at download.

  It also removes a real failure mode: today a second build directory
  configured against the same source tree re-runs the patcher against an
  already-patched submodule.

### CLI11 — Class C. Phase 2.
Header-only, `#include <CLI/CLI.hpp>`, used by one translation unit. EP with
empty configure/build and a `copy_directory` install. The
`if(NOT EXISTS lib/extlib-cli11/include/CLI/CLI.hpp) message(FATAL_ERROR ...)`
check in `tools/stp/CMakeLists.txt` must go — under an EP the header
legitimately does not exist at configure time.

### ABC — Class B. **Recommend keeping as a submodule.**
The user's Phase 2 framing is "drop the submodules and have them built by
`ExternalProject_Add`". For ABC specifically I think that is the wrong
trade, and I want to be explicit about why rather than quietly not doing it:

1. `lib/extlib-abc` points at `stp/abc`, an STP-controlled **fork**. A
   submodule is the right tool for a fork you commit to; `docs/code-guide.rst`
   documents that layout, and the reason ABC is *not* in `patches/` is
   precisely that its fixes are ordinary commits there.
2. STP reaches inside ABC's targets in four ways — `BUILD_SHARED_LIBS`
   shadowing, per-target `-Wno-error`, per-target `-ffunction-sections
   -fdata-sections` feeding a `--gc-sections` link, and
   `$<TARGET_FILE:libabc-pic>`. None survives an EP boundary.
3. The UBSan CI job exists to instrument the vendored C. An EP ABC is not
   instrumented.
4. 920 C files, ~17 MB. Under EP that is rebuilt per build directory; under
   `FetchContent`, re-downloaded per build directory.

If it must move, `FetchContent` with `FETCHCONTENT_SOURCE_DIR_ABC` pointing
at a local checkout is the only viable form — and at that point it is a
submodule with extra steps.

### mimalloc — Class B. **Recommend keeping as a submodule.**
`FetchContent` is technically viable (upstream, pinned, no local commits),
but mimalloc is the **default** `STP_ALLOCATOR`. Fetching it at configure
time means that with `ENABLE_AUTO_DOWNLOAD=OFF` — the sane default — a plain
build either fails or silently falls back to `system` malloc, which the docs
measure at ~14% slower. That is a bad default to introduce in exchange for
removing one submodule.

Revisit only if the allocator default changes.

### 6.1 Backend selection becomes explicit

All four SAT backends become ordinary opt-in options:

| Option | Today | After |
|---|---|---|
| `USE_CRYPTOMINISAT` | derived — set by `CMakeLists.txt` when `find_package` succeeds; the only user control is the negative `NOCRYPTOMINISAT` | a real option, default **OFF**; `NOCRYPTOMINISAT` kept as a deprecated alias that warns and FORCEs once |
| `USE_CADICAL` | option, default OFF | option, default **ON** — but only once CaDiCaL is auto-downloadable; see below |
| `USE_MINISAT` | option, default OFF | unchanged, default OFF |
| `USE_RISS` | option, default OFF | unchanged, default OFF |

CaDiCaL defaulting ON is what keeps the "no SAT backend is enabled" fatal
error unreachable from a plain `cmake ..`. It is the right one to pick: it
needs no system library (CryptoMiniSat drags in GMP, MiniSat drags in zlib),
it is fully auto-downloadable, and it is the backend the docs already
recommend for hard bitvector problems. The net effect is that
`git clone && ./configure.sh --auto-download && cmake --build build` works
from nothing.

**Sequencing: the two halves cannot land together.** `USE_CADICAL=ON` is only
satisfiable once `FindCaDiCaL.cmake` exists — today the lookup is
`PATHS ${CADICAL_DIR} NO_DEFAULT_PATH`, so with no `CADICAL_DIR` it finds
nothing and a defaulted-ON CaDiCaL would fail every plain `cmake ..`. And
flipping CryptoMiniSat to OFF *before* that leaves a plain `cmake ..` with no
backend at all.

So Phase 0 lands the **plumbing** and keeps today's effective defaults:
`USE_CRYPTOMINISAT` becomes a real three-valued option whose unset state still
means "use it if it is installed", so nothing breaks. Phase 1 changes one line
— the unset default becomes OFF — in the same commit that gives `USE_CADICAL`
something to find. That commit is the behaviour change; this one is not.

Two consequences to handle when that lands:

- The "no SAT backend" check currently runs *after* the CryptoMiniSat block,
  because it had to wait for auto-detection. With everything explicit it can
  run early, next to the option declarations, and say what to pass.
- A machine with CryptoMiniSat installed silently stops linking it. That is
  the point of the change, but it is a visible behaviour difference and
  belongs in the release notes, not just a commit message.

### 6.2 The rest of the auto-detection sweep

Beyond the backends, three things are still decided by what happens to be on
the build machine. Only one of them is worth an option.

**`help2man` — worth making explicit.** `find_program(HELP2MAN_FOUND
help2man)`; if it is present, `man_stp` is added to the `ALL` target and
`stp.1` is added to the install set. So *the contents of an install differ
depending on whether a tool nobody asked for is on the box*, silently, and
without appearing in the feature summary. Add a tri-state `BUILD_MANPAGE`
(`AUTO` default, preserving today's behaviour; `ON` fails loudly if
`help2man` is missing; `OFF` never builds it) and a `add_feature_info` line.
Packagers are the ones who care.

**zlib — a bug to fix, not an option.** Under `USE_MINISAT`:

```cmake
find_package(ZLIB)                        # not REQUIRED
include_directories(${ZLIB_INCLUDE_DIR})  # not checked
```

A missing zlib produces an empty include directory and a compile failure
several minutes later inside a MiniSat header. Make it
`find_package(ZLIB REQUIRED)` with a message naming `zlib1g-dev`. zlib itself
stays system-found — do **not** give it an EP; it is MiniSat's dependency,
reached only through MiniSat's public headers, exactly as GMP is
CryptoMiniSat's.

**`git` — leave alone.** `find_program(GIT_EXECUTABLE git)` falls back to
`GIT-hash-notfound` in the version string. It is a cosmetic difference and an
option would not earn its keep. (Note it does become *less* load-bearing after
Phase 2: the configure-time `git apply` of the SymFPU patches goes away.)

**Explicitly not to be made optional again: LibBF.** `USE_LIBBF` was removed
deliberately and LibBF made mandatory. Nothing here reopens that — it stays
required, and auto-download is what makes "required" cheap.

Everything else already is explicit and should stay as it is: `STP_ALLOCATOR`
(with its `tcmalloc` / `mimalloc` / `system` lookup), `USE_VALGRIND`,
`SANITIZE`, `COVERAGE`, `WERROR`, `TUNE_NATIVE`, `USE_POPCNT`,
`USE_THREAD_LOCAL`, `ENABLE_TESTING`, `BUILD_EXECUTABLES`. `lit`, Bison,
Flex and Python 3 are correctly `REQUIRED` where they are needed.

---

## 7. Phasing

### Phase 0 — prerequisites (mergeable alone) — DONE

Landed and verified; see §7.1 for what was measured.

1. `include/stp/Sat/Cadical.h`: `"src/cadical.hpp"` → `<cadical/cadical.hpp>`,
   with `CADICAL_DIR` staging the header so the current recipe keeps working.
2. Replace global `include_directories`/`link_libraries` for CaDiCaL and
   LibBF with `target_link_libraries(... PRIVATE ...)` in `lib/Sat/` and
   `lib/FloatBlaster/`.
3. Introduce `USE_CRYPTOMINISAT` as a real three-valued option — `ON`
   required, `OFF` never, unset = today's auto-detection — subsuming both
   `NOCRYPTOMINISAT` and `FORCE_CMS`, which stay as deprecated aliases that
   warn once. The *default flip* and `USE_CADICAL=ON` are deferred to Phase 1
   (§6.1). Move the "no SAT backend" check up to where all four backends are
   settled.
4. Make `ENABLE_ASSERTIONS` three-valued so `Release` stops silently
   overriding an explicit `ON`.
5. `CMAKE_MODULE_PATH` gains `${PROJECT_SOURCE_DIR}/cmake`.
6. `find_package(ZLIB REQUIRED)` under `USE_MINISAT`, and a tri-state
   `BUILD_MANPAGE` for help2man (§6.2).

Each of these is independently defensible and independently reviewable, and
together they are most of the risk.

#### 7.1 What Phase 0 actually changed, and what it was checked against

Files: `CMakeLists.txt`, `cmake/modules/STPOptions.cmake` (new),
`cmake/modules/AddSTPGTest.cmake`, `lib/CMakeLists.txt`,
`lib/Sat/CMakeLists.txt`, `lib/FloatBlaster/CMakeLists.txt`,
`include/stp/Sat/Cadical.h`, plus the call sites in `.github/`, `scripts/`
and `docs/`.

Two findings worth recording, because both were wrong in the first draft:

- **`INTERFACE_SYSTEM_INCLUDE_DIRECTORIES` alone adds nothing.** See the note
  in §4.4. Setting only that property — cvc5's recipe — compiled to a fatal
  `cadical/cadical.hpp: No such file or directory`. Both properties are now
  set on both imported targets.
- **The unit tests reach CaDiCaL's header directly.** Six of them include
  `stp/Sat/Cadical.h` under `#ifdef USE_CADICAL`, and were relying on the
  project-wide `include_directories()`/`link_libraries()` that this removes.
  `AddSTPGTest` now links the `CaDiCaL` target, which is where the old
  behaviour belonged anyway — a shared libstp localises the symbols it took
  from `libcadical.a` (`--exclude-libs`), so a test that reaches CaDiCaL needs
  its own copy, exactly as the tests that instantiate `BBNodeManagerAIG` link
  `$<TARGET_FILE:libabc-pic>`.

Verified:

| Configuration | Result |
|---|---|
| RelWithDebInfo, CaDiCaL, testing on — **before** the change | 155/155 ctest |
| RelWithDebInfo, CaDiCaL, testing on — **after** | 155/155 ctest |
| RelWithDebInfo, CryptoMiniSat, testing on | 154/154 ctest (one fewer test registered: the CaDiCaL factor sweep) |
| Release, static, CaDiCaL | builds; `libbf.a`, `libabc-pic.a` each once on the link line |
| `-isystem` scoping | CaDiCaL and LibBF include dirs now appear only on `sat` and `floatblaster`, not on every target |
| Release, nothing said | assertions off, `-DNDEBUG` present (unchanged) |
| Release + `-DENABLE_ASSERTIONS=ON` | assertions **on**, no `-DNDEBUG` — the bug this fixes |
| `-DUSE_CRYPTOMINISAT=ON`, package unfindable | configure fails, naming `cryptominisat5_DIR` and `-DUSE_CRYPTOMINISAT=OFF` |
| nothing said, CryptoMiniSat installed | auto-detected and enabled, as before |
| `-DNOCRYPTOMINISAT=ON` / `-DFORCE_CMS=ON` | warn once, translate correctly |
| no backend enabled | fails with the four-line "enable at least one of" message |
| `-DBUILD_MANPAGE=ON`, no help2man | configure fails |
| unset, no help2man | "Cannot find help2man, not creating manpage" (unchanged) |
| `-DBUILD_MANPAGE=OFF` | no `man_stp` target, no `stp.1` install rule |

Not reproducible on this machine: a fully static build **with** CryptoMiniSat,
which needs a static `libgmp.a` that is not installed here. The failure is
`cannot find -lgmp` from CryptoMiniSat's own link interface and is unrelated to
these changes — the STP-side link line was confirmed correct in that build
before the GMP step.

### Phase 1 — the script-fetched dependencies

**Phase 1 is complete.** LibBF, MiniSat, Riss and CaDiCaL are built by
ExternalProject when not found; CryptoMiniSat gets the ladder without a build
rung (see below); GTest and OutputCheck come through FetchContent;
`configure.sh` exists; the §6.1 default flips have landed with the CI sweep
they require.

The headline claim is verified end to end: from a tree with **no `deps/` at
all**, `./configure.sh --auto-download && cmake --build build` gives
**155/155 ctest**. Also green after the flips: CaDiCaL-by-default 154/154,
CryptoMiniSat 154/154, MiniSat 154/154.

Two adjustments to §6.1 as written:

- `USE_CRYPTOMINISAT`'s third state needed a real name. Once "unset" no longer
  means "auto", reusing CMake's `IGNORE` for it made the state unreachable, so
  the option is a plain three-valued string — `OFF` (default), `ON`
  (required), `AUTO` (use it if installed). `NOCRYPTOMINISAT=OFF` meant "do
  look for it", so it translates to `AUTO`, not `ON`.
- `USE_CADICAL` stayed a plain `option()` rather than becoming three-valued.
  A defaulted-ON CaDiCaL that cannot be found now produces the Find module's
  own message, which already names `--auto-download` and `-DUSE_CADICAL=OFF`
  — better than the generic "no SAT backend is enabled" a graceful degradation
  would have fallen through to.

Three findings from doing it, none of which the design anticipated:

- **Three of the four buildable dependencies fail on their own executables,
  not their libraries.** MiniSat, CryptoMiniSat and (to a lesser degree)
  CaDiCaL all put `-static` on the command-line programs they build alongside
  the library, which then needs a static `libz`, `libgmpxx`, `libstdc++` and
  `libc` on the build machine. STP runs none of those programs. Building only
  the library target is both faster and portable to machines the shell scripts
  simply failed on — this one included, which has no `libz.a` or `libgmpxx.a`.
  The consequence is that MiniSat and Riss need install steps of STP's own,
  because upstream's install rules name the programs too.
- **CryptoMiniSat cannot have a build rung at all**, and the reason is
  structural rather than effort: it reaches STP as a *CMake package*, not as a
  header and an archive, and an ExternalProject writes that package at build
  time — after the configure that must read it. Installing it by hand instead
  would leave a copy no later build could find the same way, and would make
  STP's own `STPConfig.cmake` name a package that was not there. It gets rungs
  0, 1 and a failure that names `setup-cms.sh`; §6.1's default flip still
  applies to it.
- **`deps-helper.cmake` made `CMAKE_PREFIX_PATH` a two-element list**, which
  broke the UF install-tree consumer test: its driver substituted the list into
  a command line unescaped, so every path after the first became a stray
  argument. Fixed in its own commit. Worth remembering as the general hazard —
  anything that interpolates `@CMAKE_PREFIX_PATH@` was relying on it holding
  exactly one entry.

**Step 1 detail:** `cmake/deps-helper.cmake`, `cmake/FindLibBF.cmake` and
`cmake/deps-utils/libbf-CMakeLists.txt`, wired in as
`find_package(LibBF REQUIRED)`. Verified: rung 0 (`LIBBF_DIR`) unchanged; rung
1 finds a copy installed by another build directory; rung 3 clones, patches in
the injected CMakeLists, builds and installs; the not-found error names both
`-DLIBBF_DIR` and `-DENABLE_AUTO_DOWNLOAD=ON`; the `deps` target builds the
dependency and nothing else; a second build directory sharing `STP_DEP_DIR`
creates **no** ExternalProject and needs no `--auto-download`; the
`.stp-dep-config` stamp is silent across build types and warns on a compiler
change. Full build with the ExternalProject-built LibBF: **155/155 ctest**,
`libbf.a` taken from `deps/install/lib`, real-literal folding correct.

Two adjustments to the design as written:

- The `.stp-dep-config` stamp compares only compiler, sanitizer and toolchain.
  Including the build type made it warn on the single most common legitimate
  use of a shared directory, which would have trained everyone to ignore it.
- `check_auto_download` derives the "point me at a copy" variable by
  uppercasing (`LIBBF_DIR`, `CADICAL_DIR`, `RISS_DIR`), with an optional
  override for `cryptominisat5_DIR`, which is spelled by its upstream package.

`include(deps-helper)` sits below the compiler-flag blocks rather than with the
other includes, because `STP_EP_COMMON_CMAKE_ARGS` captures `CMAKE_CXX_FLAGS`
by value. Included from the top, a sanitizer build would compile its
dependencies without the sanitizer.

**Remaining:**

`cmake/deps-helper.cmake`, `STP_EP_COMMON_CMAKE_ARGS`, the `STP_DEP_DIR` /
`--dep-dir` plumbing and the `deps` target, and Find modules for
**LibBF, CaDiCaL, CryptoMiniSat, MiniSat, Riss**; `FetchContent` for
**GTest** and **OutputCheck**; `configure.sh`.

Submodules untouched. `scripts/deps/*.sh` deleted — or kept for one release
as three-line shims that print a deprecation and call
`cmake -DENABLE_AUTO_DOWNLOAD=ON`.

Suggested order, each landable on its own: **LibBF → MiniSat → Riss →
CryptoMiniSat → CaDiCaL → GTest/OutputCheck → configure.sh → CI → docs.**
LibBF proves the mechanism on the required dependency with the simplest
build. CaDiCaL is last because of the makefile-substitution recipe and the
collision guard.

### Phase 2 — the header-only submodules — DONE

SymFPU and CLI11 are ExternalProjects (23b27370); `patches/symfpu/` moved to
`cmake/deps-utils/symfpu/`; `stp_apply_vendored_patches()` is gone; `.gitmodules`
is down to ABC and mimalloc. The six retired setup scripts and the CI rework
they allow are 9d67c8b3.

Verified: from a tree carrying **only the two remaining submodules** —
no `deps/`, no CLI11, no SymFPU — `./configure.sh --auto-download` gives
**155/155 ctest**.

Three notes from doing it:

- **A tarball, not a git clone, for SymFPU** — and not as a preference.
  ExternalProject's update step for a git source re-runs `git checkout`, which
  reverts a patched working tree. `URL` has no update step to fight.
- **SymFPU had to go on `stp`'s `BUILD_INTERFACE`, not on a list of targets.**
  `stp/FloatBlaster/symbolic_fp.h` is an internal header that includes
  `symfpu/core/unpackedFloat.h`, and anything in the tree may include it — the
  hand-written list of consumers was wrong by two targets (`test_fpbackend`,
  `test_fprewrites`) the first time it was written. `BUILD_INTERFACE` keeps it
  out of the exported `STPTargets.cmake`, where no consumer has such a target
  and none needs one.
- **CMake refuses to mix the plain and keyword `target_link_libraries`
  signatures on one target.** `stp-bin` uses the plain form, so CLI11 is named
  inside that call rather than in a second one.

### Phase 2 — the header-only submodules (as designed)

**SymFPU** and **CLI11** become EPs; `patches/symfpu/` moves to
`cmake/deps-utils/`; `stp_apply_vendored_patches()` is deleted; `.gitmodules`
loses two entries.

### Phase 2b — ABC and mimalloc — DONE (4f9356cc)

Landed at the user's direction, over the recommendation in §6. STP now has no
submodules at all: `git clone` plus a configure is the whole recipe, and
**155/155 ctest** from a tree containing nothing but STP's own sources.

The §6 objections were about workflow, not feasibility, and both were
addressed rather than ignored:

- **The ABC fork workflow survives** through
  `-DFETCHCONTENT_SOURCE_DIR_ABC=<clone>`, which makes the build use a
  checkout in place and fetch nothing, so it can still be edited, committed
  and pushed from where it is before `ABC_GIT_TAG` moves. Verified end to end.
  It is one step more than committing inside a submodule, and that is the real
  cost of this change.
- **mimalloc fails loudly** rather than falling back to system malloc, so the
  ~14% regression the §6 objection worried about cannot happen silently.

Mechanically: both use `FetchContent` with a `SOURCE_SUBDIR` that does not
exist, which is what stops `FetchContent_MakeAvailable()` calling
`add_subdirectory()` itself — each needs `EXCLUDE_FROM_ALL`, and
`MakeAvailable` could not be told that until CMake 3.28, well past STP's 3.18
floor. ABC is populated in the top-level `CMakeLists.txt` (which needs its
include directory) and added from `lib/CMakeLists.txt` (which has its build
settings).

One thing this broke and repaired:
`scripts/extdiff-baseline-differential.sh` builds a baseline commit from
history whose tree still expects both submodules, and it used to link them
from the candidate's submodule directories. It now links them from wherever
the candidate's FetchContent put them.

### Phase 2b — ABC and mimalloc (the original recommendation, overruled)

Only if the reasons above are judged not to hold. `FetchContent`, never
`ExternalProject`.

---

## 8. Risks and decisions

### 8.1 A shared dependency directory is not keyed by configuration — RESOLVED, with a residual

Design settled in §4.2: `--dep-dir=PATH` / `STP_DEP_DIR` is the shared
*install* tree (inherit **and** install); the EP `PREFIX` stays per-build so
stamp files never race; the default is `${PROJECT_BINARY_DIR}/deps`; the
source tree's `deps/install` stays on `CMAKE_PREFIX_PATH` for
back-compatibility.

Two residuals, both documented rather than engineered away:

- A shared directory holds one `libcadical.a` regardless of the compiler,
  build type or sanitizer that produced it. Mitigated by the
  `.stp-dep-config` stamp and a `message(WARNING)` naming the mismatched
  fields.
- Two *concurrent first* configures against one `--dep-dir` both build and
  both install. Warm the directory once with the `deps` target (§5.6).

### 8.2 Configure-time network access — RESOLVED

`ENABLE_AUTO_DOWNLOAD`, default **OFF**, surfaced as `--auto-download`.
`./configure.sh` does **not** imply it: a build that reaches the network
should say so, and the error message that names the flag is half the feature.
The headline recipe is therefore
`./configure.sh --auto-download`.

Two things to get right:

- **`FetchContent` needs a hand-written gate.** GTest and OutputCheck
  download at *configure* time, not build time, and `FetchContent` has no
  equivalent of `check_auto_download`. Guard both on
  `ENABLE_TESTING AND ENABLE_AUTO_DOWNLOAD`, and honour
  `FETCHCONTENT_SOURCE_DIR_<NAME>` so an offline or distro build can point at
  an existing checkout.
- **`--dep-dir` largely retires the flag.** Once a shared directory is warm,
  every dependency resolves at rung 1 and no download is attempted, so
  `--auto-download` is needed on the first configure only. Say so in
  `docs/building.rst`; it is the difference between "this project downloads
  things behind my back" and "this project downloaded things once, when I
  asked".

### 8.3 Tarball hashes vs git pins
cvc5 uses `URL` + `URL_HASH SHA256` throughout, relying on GitHub's
auto-generated archive tarballs being byte-stable. They have not always
been. For **upstream release tags** (CryptoMiniSat, googletest) the risk is
low and the reproducibility win is real. For **STP's own forks** (`stp/libbf`,
`stp/minisat`, `stp/OutputCheck`) the pins are *commits* on rebased branches,
which have no tarball at all — use `GIT_REPOSITORY` + `GIT_TAG <sha>` there.

Recommendation: `URL`+`URL_HASH` where a stable release tag exists,
`GIT_REPOSITORY`+`GIT_TAG <full sha>` otherwise. Never `GIT_TAG <branch>`.

### 8.4 CI blast radius
13 jobs in `ci.yml` plus `codeql-analysis.yml`, `release.yml`, the
`build-static-linux` composite action, `scripts/ci-32bit.sh`, `Dockerfile`,
`Docker.ubuntu22`, and 6 documentation files. 67 references to
`scripts/deps/setup-*.sh` / `cache-key.sh` in total.

Two specific changes:
- Every `actions/cache` `path:` (`deps/install`, `deps/cadical`,
  `deps/gtest`, `deps/OutputCheck`) becomes a path under the build directory,
  which couples the dependency cache to the build directory name.
- `scripts/deps/cache-key.sh` becomes `sha256(cmake/Find*.cmake
  cmake/deps-helper.cmake)` and loses its `git ls-remote` (once OutputCheck
  is pinned) — so it stops needing the network and stops being a per-run
  variable.

### 8.5 EP logs are hidden by default
`COMMON_EP_CONFIG` sets `LOG_DOWNLOAD/UPDATE/CONFIGURE/BUILD/INSTALL ON`,
which sends output to files instead of the console. Today a failing
`setup-cms.sh` prints its error in the CI log. `LOG_OUTPUT_ON_FAILURE ON` and
`LOG_MERGED_STDOUTERR ON` (both in cvc5's config, both ≥ CMake 3.14, and
STP's floor is 3.18) restore that — do not omit them.

### 8.6 The auto-detection→explicit flip — RESOLVED

All four backends become opt-in; `USE_CADICAL` defaults ON so a plain
`cmake ..` still has a backend. Full detail, including the two consequences
that come with it, in §6.1. The wider sweep of what else is decided by
machine state — `help2man`, zlib, `git` — is in §6.2.

This is a visible behaviour change for anyone with CryptoMiniSat installed,
and it wants its own commit and its own release-note line.

### 8.7 Static builds are where the export breaks
See §4.7. `STATICCOMPILE=ON` is what `release.yml`, `Dockerfile` and the
Windows job use. Test it early, not at the end.

---

## 8.8 What is still open

Measured or observed during the work, not speculation.

**1. An installed *static* STP exported paths a consumer could not resolve — FIXED.** The
generated `STPTargets.cmake` carries

```
INTERFACE_LINK_LIBRARIES "<dep-dir>/lib/libabc-pic.a;<src>/deps/libbf/libbf.a;<prefix>/lib64/libcadical.a"
```

The archives themselves *are* installed alongside libstp — `install(FILES
${X_LIBRARY} …)` when `NOT BUILD_SHARED_LIBS` — but the export points at the
originals rather than the installed copies, so the package is only usable on
the machine that built it.

This predates the migration in shape: the note above `target_link_libraries(stp
PRIVATE …)` records that PRIVATE was chosen to keep these out of the export,
which is true of a *shared* libstp (private dependencies do not propagate) and
false of a static one (they propagate as `$<LINK_ONLY:>`). What has changed is
that the paths now point into a dependency directory explicitly meant to be
shared between builds or thrown away, so the breakage is easier to hit.

**Fixed (6c55055b).** Every absolute path to a static archive on libstp's link
line is installed beside libstp and named `$<INSTALL_INTERFACE:$<INSTALL_PREFIX>/…>`
in the export. Two things the first attempt got wrong, both worth recording:

- Keying the rewrite on *provenance* — "we fetched it, so we install it" — was
  not enough. LibBF and CaDiCaL had been *found*, in `deps/libbf` and
  `deps/install`, and a path inside the source tree is no more portable than a
  fetched one. The test has to be the shape of the entry: an absolute path to a
  static archive gets shipped, anything else (`-lgmp`, `-lz`, a shared library)
  passes through.
- `$<INSTALL_PREFIX>` rather than a literal prefix, or the package stops
  working the moment it is moved.

And a check, because nothing would have caught it: the static build action
installs, **moves the installation, the build tree and the dependency directory
out of the way**, and builds the existing consumer project against what
remains. Moving them first is the whole point — without it the check passes on
paths that merely happen to still be there, which is exactly how the broken
behaviour passed.

Verified by hand the same way. The shared build's export stays empty of these
entries, as it always was.

**2. CryptoMiniSat's version was not checked — FIXED (d8f0c1b4).** A floor of
5.11, chosen from evidence: it is the oldest release anything in the repository
builds (both Dockerfiles do), and every method `lib/Sat/CryptoMinisat5.cpp`
calls exists in it — checked against a 5.11.21 checkout rather than assumed.
Older ones are refused for being untested, not for being known broken, and the
error says so.

The version is compared in the module rather than passed to `find_package`, so
that a too-old copy is reported as too old. Handing the version to
`find_package` would have produced "could not find CryptoMiniSat" about a
library that is plainly installed.

(A near-miss worth recording: `printStats` appears in STP's call list and *not*
in CryptoMiniSat 5.11's header, which looked like the floor was wrong. It is
STP's own method on its `CryptoMiniSat5` wrapper, with a commented-out body —
it calls nothing.)

**3. `configure.sh` had no `--abc-dir` — FIXED (cf6ebae3),** along with an
audit for references to things this branch deleted. Three of those were error
messages a user reaches, not comments: the "no SAT backend is enabled" message
named `setup-cadical.sh`, and the GoogleTest and OutputCheck failures each
named their setup script. `stp --version` also reported two dead variables —
`LIBS`, removed with the MiniSat work, and `FORCE_CMS`, now an alias that is
empty in every build that does not use it.

**4. Concurrent first-configures against one `--dep-dir` still race.** Named in
§4.2, mitigated by the `deps` target, not enforced.

**5. The `~3.4MB` figure in the `--gc-sections` note is stale.** Measured 6.6 MB
in Release before this work and 6.7 MB after. Correcting it properly needs the
without-`--gc-sections` number too, which was not measured.

**6. Windows and MinGW are reasoning, not testing.** Nothing in this work was
run under MSVC or MinGW, and both are where the most code was removed.

---

## 9. Explicitly out of scope

- **Bison, Flex, Python 3, lit.** Toolchain, not payload. (cvc5 does
  `pip install` into a build venv for its Python tooling; STP could do the
  same for `lit`, but that is a separate question from this migration.)
- **zlib and GMP.** Reached only transitively, through MiniSat's public
  headers and CryptoMiniSat's config file respectively. Keep them
  system-found; `docs/building.rst` already names the packages.
- **tcmalloc, help2man, valgrind.** Optional, system-found, correctly so.
- **`lib/extlib-constbv`, `lib/extlib-unordered-dense`.** Vendored source,
  not dependencies.
- **`windows/`, `Docker.ubuntu22`, `scripts/starexec/`.** Downstream of the
  above; they get updated, not redesigned.

---

## 10. Summary of what changes

| | Before | After |
|---|---|---|
| Get a buildable tree | `git submodule update --init`, 1–5 `scripts/deps/*.sh`, then `cmake` | `./configure.sh --auto-download` (first time only, with `--dep-dir`) |
| Where pins live | 8 shell scripts | 8 `cmake/Find*.cmake`, beside the logic that uses the version |
| Toolchain reaches deps | no | yes (compiler, flags, launcher, sysroot, toolchain file, PIC) |
| macOS | 5 of 8 scripts are GNU-only | works |
| Windows | bespoke PowerShell per dependency | same CMake path as everywhere else |
| Dep location | `<source>/deps`, shared, no way to opt out | `<build>/deps` by default; `--dep-dir=P` to inherit-and-install into a shared tree; legacy `deps/install` still honoured |
| Where deps are declared | shell + CMake, in different places | one file per dependency |
| Backend selection | CryptoMiniSat auto-detected — depends on the machine | all four opt-in; `USE_CADICAL` defaults ON |
| Submodules | 4 | 2 after Phase 2 (ABC, mimalloc — deliberately) |
| `patches/symfpu` machinery | 60 lines of configure-time idempotency logic | `PATCH_COMMAND` |
| CI cache key | hash of scripts + a live `git ls-remote` | hash of `cmake/Find*.cmake` |
