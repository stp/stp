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

    python3 -m venv venv
    ./venv/bin/pip install -r docs/requirements.txt
    ./venv/bin/sphinx-build -W -b html docs _site

Then open `_site/index.html`. `-W` turns warnings into errors, which is what
CI does, so a build that passes locally will not fail there.

`sphinx-build` rebuilds only what changed. Pass `-E` if you have edited
`conf.py`, a template or `_static/custom.css` and want the whole site
regenerated: an incremental build can leave the previous stylesheet in place.

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
