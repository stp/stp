# STP website and manual

The sources for <https://stp.github.io/stp/>, which <https://stp.github.io/>
redirects to. Landing page and manual are one Sphinx build; there is no
separate site generator. `.github/workflows/pages.yml` publishes it on every
merge to master, and builds it without publishing on pull requests.

`index.rst` is the landing page. Pages reached from its `toctree` directives
appear in the sidebar navigation on every page, so a new page needs to be
listed under one of them.

`_extra/` is copied into the build verbatim. It holds a redirect stub per page
for `/stp/docs/`, where the manual was published before it was merged with the
landing page; the stubs keep links from elsewhere working.

## Building it locally

Use Python 3.10 or later (CI uses 3.12), Doxygen, and the normal STP build
dependencies. On Ubuntu, the native tools are `build-essential`, `cmake`,
`ninja-build`, `bison`, `flex`, `doxygen`, `python3-dev` and `python3-venv`.

    python3 -m venv venv
    ./venv/bin/pip install -r docs/requirements.txt
    cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release \
        -DENABLE_AUTO_DOWNLOAD=ON -DUSE_CRYPTOMINISAT=OFF \
        -DENABLE_PYTHON_API=ON -DPYTHON_EXECUTABLE="$PWD/venv/bin/python"
    cmake --build build --target stp_python --parallel 4
    ./venv/bin/python docs/build.py --build-dir build --output docs/_build/html

Then open `docs/_build/html/index.html`, or serve it locally:

    ./venv/bin/python -m http.server --directory docs/_build/html 8000

The documentation interpreter must match the one used to build the Python
extension. An existing build with `ENABLE_PYTHON_API=ON` works too: rebuild
the `stp_python` target and pass its directory to `--build-dir`.

`build.py` copies the manual into `<build>/docs/source`, adds the reference
pages there, and runs Sphinx with warnings treated as errors. Generated RST,
Doxygen XML and HTML stay in build directories. The script does not install
STP or fetch dependencies; those steps belong to the explicit setup above.

## API reference prototype

This branch investigates [issue #283](https://github.com/stp/stp/issues/283)
for the 3.x C, C++ and Python APIs, following
[cvc5's approach](https://github.com/cvc5/cvc5/tree/cvc5-1.4.1/docs/api).

* **C and C++:** Doxygen extracts XML from `stp.h`, `stp.hpp` and the
  public headers generated from `lib/Api/tables`. Breathe renders it inside
  Sphinx. C pages follow the sections in `stp.h`; C++ classes have individual
  pages, with their nested types included. Enum/struct typedef aliases are
  rendered once so Sphinx can assign unambiguous C cross-references.
* **Python:** Sphinx autodoc imports the actual built `stp` package. Its
  `__all__` supplies the public names, including aliases, and inherited
  methods bring in the Cython base classes. A signature hook uses Python
  introspection: an inherited Cython docstring must not replace a wrapper's
  signature (for example, `Solver.set_args(*argv)` with `set_args(argv)`).
  No mock extension is used.
* **Publishing:** the existing Pages workflow builds the binding, then
  the reference and manual together. Changes to the API inputs also trigger
  a documentation build. The existing theme and hosting are retained.

The principal cost is the native build needed for Python introspection.
C/C++ extraction itself only needs the headers and Doxygen. The build helper
stages the documentation so generated pages do not become another checked-in
copy of the API. It currently regenerates the reference on each invocation.

Reference coverage and descriptive coverage differ: `EXTRACT_ALL` and
autodoc's `undoc-members` include declarations even when they have no prose.
Many existing C comments have been marked for Doxygen, but inline parameter
notes remain plain comments, and some C parameters have no names in their
declarations. Functions without comments and Python functions without
docstrings still need descriptions.
The API guide remains the place for examples and explanations across calls.

Before adopting this as the permanent reference, review the automatically
chosen page boundaries and navigation, and fill the most useful description
gaps. The prototype deliberately documents the 3.x public interfaces; the
legacy compatibility library retains its existing documentation.

### Local validation

Built from `upstream/master` at `1e29139c6`, with Python 3.12.12, Cython 3.3.0,
Doxygen 1.14.0, Breathe 4.36.0 and Sphinx 8.1.3:

* The native `stp_python` target compiled successfully.
* Doxygen and Sphinx completed with warnings treated as errors.
* All 19,366 local links across the 325 HTML pages resolved, including anchors.
* The Sphinx inventory includes generated C/C++ constructors, solver calls,
  inherited Python methods and comparison operators. Rendered Python wrapper
  signatures were checked against the actual callables.
* C99 and C++17 preprocessing produced identical output for the public headers
  before and after the documentation markup changes.
* C, C++ and Python reference pages were inspected in Chromium. The proposed
  Pages workflow parses as YAML; it has not been run on GitHub.

## Theme

The design is based on [Compass][theme] by Eduardo Rubio, ported onto Sphinx's
alabaster theme -- the palette and typography live in `conf.py` and
`_static/custom.css`. The license is reproduced below:

[theme]: http://excentris.net/compass/

    The MIT License (MIT)

    Copyright (c) 2015 Eduardo Rubio

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in all
    copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
    SOFTWARE.
