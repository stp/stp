# AUTHORS: Andrew Teylu
#
# BEGIN DATE: September, 2026
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

"""pip-install bindings/python on its own, against a staged installation of
this build, and import it.

Usage: pip_install_test.py <bindings/python> <cmake> <build dir> <install prefix> <scratch dir> [<config>]

Exits 77, which ctest reports as skipped, on Windows, where pip does not
build the package, and when this interpreter cannot build it offline: no
pip, no Cython 3, a setuptools older than pyproject.toml needs, or one that
cannot build a wheel.
"""

import os
import shutil
import subprocess
import sys

SKIP = 77

QUERY = """
import sys
import stp
from stp import BitVec, Solver, unsat
x = BitVec('x', 8)
s = Solver()
s.add(x + x != 2 * x)
assert s.check() == unsat, 'the pip-installed package gave the wrong answer'
print(stp._core.__file__)
if sys.platform.startswith('linux'):
    with open('/proc/self/maps') as maps:
        print(next(line.split()[-1] for line in maps if '/libstp.so' in line))
"""


def main():
    source, cmake, build, install_prefix, scratch = sys.argv[1:6]
    config = sys.argv[6] if len(sys.argv) > 6 else ""

    if os.name == "nt":
        print("skipped: pip does not build the package on Windows")
        return SKIP
    try:
        # setuptools first: pip imports the standard library's distutils,
        # which setuptools' distutils shim then refuses.
        import setuptools
        import pip  # noqa: F401
        import Cython
    except ImportError as e:
        print("skipped: %s" % e)
        return SKIP
    if int(setuptools.__version__.split(".")[0]) < 61:
        print("skipped: setuptools %s predates pyproject metadata" % setuptools.__version__)
        return SKIP
    if int(Cython.__version__.split(".")[0]) < 3:
        print("skipped: Cython %s is older than pyproject.toml asks for" % Cython.__version__)
        return SKIP
    try:
        # setuptools builds wheels itself from 70.1; before that it needs wheel.
        from setuptools.command import bdist_wheel  # noqa: F401
    except ImportError:
        try:
            import wheel  # noqa: F401
        except ImportError:
            print("skipped: setuptools %s cannot build a wheel without the wheel package"
                  % setuptools.__version__)
            return SKIP

    shutil.rmtree(scratch, ignore_errors=True)
    stage = os.path.join(scratch, "stage")
    src = os.path.join(scratch, "src")
    site = os.path.join(scratch, "site")

    # What pip builds against is an installation, so make one, staged under
    # DESTDIR: unlike --prefix, that also moves a destination configured as
    # an absolute path, which would otherwise need root.
    install = [cmake, "--install", build]
    if config:
        install += ["--config", config]
    subprocess.check_call(install, stdout=subprocess.DEVNULL,
                          env=dict(os.environ, DESTDIR=stage))
    prefix = os.path.join(stage, os.path.abspath(install_prefix).lstrip(os.sep))

    # A copy, because pip builds in place and would leave build/ and
    # stp.egg-info in the checkout.
    shutil.copytree(source, src)

    env = dict(os.environ)
    for var in ("STP_INCLUDE_DIR", "STP_LIBRARY_DIR", "LD_LIBRARY_PATH",
                "DYLD_LIBRARY_PATH", "PYTHONPATH"):
        env.pop(var, None)
    env["STP_PREFIX"] = prefix
    subprocess.check_call(
        [sys.executable, "-m", "pip", "install", "--no-build-isolation",
         "--no-deps", "--no-index", "--disable-pip-version-check",
         "--target", site, src], env=env)

    if not os.path.isfile(os.path.join(site, "stp", "_gen_kinds.py")):
        print("pip installed no stp/_gen_kinds.py")
        return 1

    # From the scratch directory, with nothing on the search paths, so the
    # package can only be the one pip installed and libstp only what its
    # rpath names.
    env.pop("STP_PREFIX")
    env["PYTHONPATH"] = site
    out = subprocess.check_output([sys.executable, "-c", QUERY], env=env,
                                  cwd=scratch).decode().split()
    if not os.path.abspath(out[0]).startswith(os.path.abspath(site) + os.sep):
        print("imported stp._core from %s, not from %s" % (out[0], site))
        return 1
    print("ok: the pip-installed package solves a query")
    if len(out) > 1:
        if not os.path.abspath(out[1]).startswith(os.path.abspath(prefix) + os.sep):
            print("loaded %s, not the libstp under %s" % (out[1], prefix))
            return 1
        print("ok: it loads %s" % out[1])
    return 0


if __name__ == "__main__":
    sys.exit(main())
