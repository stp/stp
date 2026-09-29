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

"""Builds stp._core for ``python3 -m pip install ./bindings/python``.

The extension is compiled against an STP that is already installed: its
headers, the generated sources its install ships for this build in
include/stp/api/python, and its libstp, which the extension then finds
through an rpath. README.md says where the installation is looked for.
"""

import os
import shutil
import sys

from Cython.Build import cythonize
from setuptools import Extension, setup
from setuptools.command.build_py import build_py

if sys.platform == "darwin":
    LIBRARY = "libstp.dylib"
elif os.name == "nt":
    sys.exit("pip cannot build the stp package on Windows; build STP with "
             "-DENABLE_PYTHON_API=ON instead")
else:
    LIBRARY = "libstp.so"

GENERATED = ("_gen_enums.pxi", "_gen_kinds.py")


def candidate_prefixes():
    """STP_PREFIX alone when it is set, else the prefix of the stp on PATH,
    /usr/local and /usr, in that order."""
    if os.environ.get("STP_PREFIX"):
        return [os.environ["STP_PREFIX"]]
    prefixes = []
    stp = shutil.which("stp")
    if stp:
        prefixes.append(os.path.dirname(os.path.dirname(os.path.realpath(stp))))
    return prefixes + ["/usr/local", "/usr"]


def usable(include_dir, library_dir):
    generated = os.path.join(include_dir, "stp", "api", "python")
    return (os.path.isfile(os.path.join(include_dir, "stp", "stp.h"))
            and all(os.path.isfile(os.path.join(generated, f)) for f in GENERATED)
            and os.path.isfile(os.path.join(library_dir, LIBRARY)))


def locate():
    """The include and library directories of the installation to build
    against. STP_INCLUDE_DIR and STP_LIBRARY_DIR name them outright."""
    tried = []
    for prefix in candidate_prefixes():
        include_dir = os.environ.get("STP_INCLUDE_DIR") or os.path.join(prefix, "include")
        if os.environ.get("STP_LIBRARY_DIR"):
            library_dirs = [os.environ["STP_LIBRARY_DIR"]]
        else:
            library_dirs = [os.path.join(prefix, "lib64"), os.path.join(prefix, "lib")]
        for library_dir in library_dirs:
            tried.append("  headers in %s, %s in %s" % (include_dir, LIBRARY, library_dir))
            if usable(include_dir, library_dir):
                return os.path.abspath(include_dir), os.path.abspath(library_dir)
    sys.exit("no installed STP to build the stp package against; tried\n%s\n"
             "An installation of this STP has stp/stp.h and stp/api/python/{%s} "
             "among its headers, and a shared %s. Set STP_PREFIX to the prefix "
             "STP was installed to, or STP_INCLUDE_DIR and STP_LIBRARY_DIR."
             % ("\n".join(tried), ",".join(GENERATED), LIBRARY))


INCLUDE_DIR, LIBRARY_DIR = locate()
GENERATED_DIR = os.path.join(INCLUDE_DIR, "stp", "api", "python")


class BuildPy(build_py):
    """The package's modules, and the generated one the installation ships."""

    def run(self):
        super().run()
        self.copy_file(os.path.join(GENERATED_DIR, "_gen_kinds.py"),
                       os.path.join(self.build_lib, "stp", "_gen_kinds.py"))


# The rpath is what lets `import stp` find this libstp with nothing set; macOS
# is given it as a linker flag, which every setuptools passes through.
core = Extension(
    "stp._core",
    sources=["stp/_core.pyx"],
    include_dirs=[INCLUDE_DIR],
    library_dirs=[LIBRARY_DIR],
    libraries=["stp"],
    runtime_library_dirs=[] if sys.platform == "darwin" else [LIBRARY_DIR],
    extra_link_args=["-Wl,-rpath," + LIBRARY_DIR] if sys.platform == "darwin" else [],
    # Cython's generated C is not this project's code: keep its warnings quiet.
    extra_compile_args=["-w"],
)

setup(
    ext_modules=cythonize([core], include_path=[GENERATED_DIR],
                          language_level=3,
                          build_dir=os.path.join("build", "cython")),
    cmdclass={"build_py": BuildPy},
)
