# STP website

The Jekyll sources for <https://stp.github.io/stp/>, which
<https://stp.github.io/> redirects to. Built and published by
`.github/workflows/pages.yml` together with the Sphinx manual in `docs/`,
which is served at `/stp/docs/`.

Links are written as `{{ site.baseurl }}/...` because the site is served from a
project path rather than the domain root; `baseurl` is set in `_config.yml`.

# Theme

The web design is based on [Compass][theme] by Eduardo Rubio. The license is reproduced below:

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
