#!/usr/bin/env python3
"""Build the manual and API reference against a configured STP build tree."""

import argparse
import enum
import inspect
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ET


ROOT = Path(__file__).resolve().parents[1]


def write_page(path, title, body):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"{title}\n{'=' * len(title)}\n\n{body}\n", encoding="utf-8")


def toctree(names):
    return ".. toctree::\n   :maxdepth: 1\n\n" + "".join(f"   {name}\n" for name in names)


def extract(build, language):
    suffix = "hpp" if language == "cpp" else "h"
    headers = [ROOT / f"include/stp/stp.{suffix}"]
    headers += sorted((build / "generated/include/stp/api/gen").glob(f"*.{suffix}"))
    # The declarations are in kind_ctors.hpp; these are their inline bodies.
    headers = [p for p in headers if p.name != "kind_ctor_templates.hpp"]
    output = build / "docs/doxygen" / language
    output.mkdir(parents=True, exist_ok=True)
    settings = {
        "PROJECT_NAME": "STP",
        "INPUT": " ".join(f'"{p}"' for p in headers),
        "OUTPUT_DIRECTORY": f'"{output}"',
        "INCLUDE_PATH": f'"{build / "generated/include"}"',
        "GENERATE_XML": "YES",
        "GENERATE_HTML": "NO",
        "GENERATE_LATEX": "NO",
        "QUIET": "YES",
        "EXTRACT_ALL": "YES",
        "EXTRACT_PRIVATE": "NO",
        "EXTRACT_STATIC": "NO",
        "ENABLE_PREPROCESSING": "YES",
        "MACRO_EXPANSION": "YES",
        "EXPAND_ONLY_PREDEF": "YES",
        "PREDEFINED": "STP_API= STP_API_EXPORT= STP_API_EXPORT_INLINE=",
        "EXCLUDE_SYMBOLS": "stp::api::detail stp::api::detail::* std::*",
        "WARN_IF_UNDOCUMENTED": "NO",
        "WARN_AS_ERROR": "FAIL_ON_WARNINGS",
        "OPTIMIZE_OUTPUT_FOR_C": "YES" if language == "c" else "NO",
    }
    config = output / "Doxyfile"
    config.write_text("\n".join(f"{k} = {v}" for k, v in settings.items()) + "\n")
    subprocess.run(["doxygen", str(config)], cwd=ROOT, check=True)
    return output / "xml"


def cpp_pages(xml, dest):
    index = ET.parse(xml / "index.xml").getroot()
    pages = []
    for compound in index.findall("compound"):
        name = compound.findtext("name")
        kind = compound.get("kind")
        if kind not in ("class", "struct") or not name.startswith("stp::api::"):
            continue
        short = name.removeprefix("stp::api::")
        # Breathe includes nested types on their enclosing class's page.
        if "::" in short:
            continue
        filename = short.replace("::", "-")
        pages.append(filename)
        write_page(dest / f"{filename}.rst", short,
                   f".. doxygen{kind}:: {name}\n   :project: stp-cpp\n"
                   "   :members:\n   :undoc-members:\n")
    namespace_id = next(c.get("refid") for c in index.findall("compound")
                        if c.get("kind") == "namespace" and c.findtext("name") == "stp::api")
    namespace = ET.parse(xml / f"{namespace_id}.xml").getroot()
    enums = []
    functions = []
    for member in namespace.findall(".//sectiondef/memberdef"):
        name = member.findtext("name")
        if member.get("kind") == "enum":
            enums.append(name)
        elif member.get("kind") == "function":
            signature = name + member.findtext("argsstring", "()")
            functions.append(f".. doxygenfunction:: stp::api::{signature}\n   :project: stp-cpp\n")
        elif member.get("kind") == "typedef":
            functions.append(f".. doxygentypedef:: stp::api::{name}\n   :project: stp-cpp\n")
    write_page(dest / "enums.rst", "Enumerations",
               "\n".join(f".. doxygenenum:: stp::api::{name}\n   :project: stp-cpp\n"
                         for name in sorted(set(enums))))
    write_page(dest / "functions.rst", "Functions and operators",
               "\n".join(functions))
    write_page(dest / "index.rst", "C++ API",
               "Include ``<stp/stp.hpp>`` and link against ``libstp``. C++17 is required.\n\n"
               "The header makes the names in ``stp::api`` available directly in ``stp``: "
               "for example, write ``stp::Solver`` and ``stp::TermManager``.\n\n"
               + toctree(pages + ["functions", "enums"]))


def c_pages(xml, dest):
    # Keep the header's organization, while rendering typedefs of named enums
    # and structs only once. Sphinx's C domain otherwise sees duplicate names.
    sections = []
    groups = {}
    for line, text in enumerate((ROOT / "include/stp/stp.h").read_text().splitlines(), 1):
        match = re.match(r"/\* -+ (.*?) \*/", text)
        if match:
            title = match[1].split(" (")[0].split(":")[0].capitalize()
            slug = title.lower().replace(" ", "-")
            sections.append((line, slug))
            groups[slug] = (title, [])
    for compound in ET.parse(xml / "index.xml").getroot().findall("compound"):
        if compound.get("kind") not in ("file", "struct"):
            continue
        tree = ET.parse(xml / (compound.get("refid") + ".xml")).getroot()
        if compound.get("kind") == "struct":
            members = [(tree.find("compounddef"), "struct", compound.findtext("name"))]
        else:
            members = [(m, m.get("kind"), m.findtext("name"))
                       for m in tree.findall(".//sectiondef/memberdef")]
        for member, kind, name in members:
            if kind not in ("function", "typedef", "enum", "struct", "define"):
                continue
            type_text = "".join(member.find("type").itertext()) if member.find("type") is not None else ""
            if kind == "typedef" and type_text in (f"enum {name}", f"struct {name}"):
                continue
            location = member.find("location")
            if location is None:
                continue
            header = Path(location.get("file")).name
            if header == "stp.h":
                line = int(location.get("line"))
                slug = next(s for start, s in reversed(sections) if start <= line)
            elif header == "kind_ctors.h":
                slug = "named-constructors"
            elif header in ("kinds.h", "options.h", "errors.h"):
                slug = "enums"
            else:
                continue
            body = f".. doxygen{kind}:: {name}\n   :project: stp-c\n"
            if kind == "struct":
                body += "   :members:\n   :undoc-members:\n"
            groups[slug][1].append(body)
    pages = []
    for slug, (title, directives) in groups.items():
        if directives:
            pages.append(slug)
            write_page(dest / f"{slug}.rst", title, "\n".join(directives))
    write_page(dest / "index.rst", "C API",
               "Include ``<stp/stp.h>`` and link against ``libstp``. "
               "See :doc:`../../api` for examples and error handling.\n\n"
               ".. doxygenfile:: stp.h\n   :project: stp-c\n"
               "   :sections: briefdescription detaileddescription\n\n"
               + toctree(pages))


def python_pages(package, dest):
    sys.path.insert(0, str(package))
    import stp

    if Path(stp.__file__).resolve().parent != package / "stp":
        raise RuntimeError(f"Imported {stp.__file__}, expected the package in {package}")
    sections = {"Classes": [], "Functions": [], "Constants": []}
    for name in stp.__all__:
        obj = getattr(stp, name)
        if inspect.isclass(obj):
            sections["Classes"].append(name)
            body = f".. autoclass:: stp.{name}\n   :members:\n   :undoc-members:\n"
            if not issubclass(obj, (enum.Enum, BaseException)):
                body += "   :inherited-members:\n"
                body += ("   :special-members: __call__, __getitem__, __setitem__, __iter__, "
                         "__len__, __contains__, __enter__, __exit__, __bool__, __eq__, __ne__, "
                         "__lt__, __le__, __gt__, __ge__, __add__, __radd__, __sub__, __rsub__, "
                         "__mul__, __rmul__, __truediv__, __rtruediv__, __mod__, __rmod__, "
                         "__and__, __rand__, __or__, __ror__, __xor__, __rxor__, __lshift__, "
                         "__rshift__, __neg__, __invert__, __int__, __float__\n")
        elif callable(obj):
            sections["Functions"].append(name)
            body = f".. autofunction:: stp.{name}\n"
        else:
            sections["Constants"].append(name)
            body = f".. autodata:: stp.{name}\n"
        write_page(dest / f"{name}.rst", f"stp.{name}", body)
    body = "Import the ``stp`` package. See :doc:`../../api` for examples and API conventions.\n\n"
    for title, names in sections.items():
        body += f"{title}\n{'-' * len(title)}\n\n" + toctree(names) + "\n"
    write_page(dest / "index.rst", "Python API", body)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", type=Path, default=ROOT / "build")
    parser.add_argument("--output", type=Path, default=ROOT / "docs/_build/html")
    args = parser.parse_args()
    build = args.build_dir.resolve()
    package = build / "bindings/python"
    cache = build / "CMakeCache.txt"
    if not cache.is_file() or f"CMAKE_HOME_DIRECTORY:INTERNAL={ROOT}" not in cache.read_text().splitlines():
        parser.error("--build-dir must be an STP build configured from this checkout")
    if not (package / "stp/__init__.py").is_file():
        parser.error("Build the Python API first: cmake --build <build-dir> --target stp_python")
    source = build / "docs/source"
    if source.exists():
        shutil.rmtree(source)
    shutil.copytree(ROOT / "docs", source, ignore=shutil.ignore_patterns("_build", "__pycache__"))
    cpp_pages(extract(build, "cpp"), source / "reference/cpp")
    c_pages(extract(build, "c"), source / "reference/c")
    python_pages(package, source / "reference/python")
    env = dict(os.environ, STP_DOCS_BUILD_DIR=str(build))
    # A fresh environment also clears C-domain declarations when a generated
    # page is renamed or its members move to a different page.
    subprocess.run([sys.executable, "-m", "sphinx", "-E", "-W", "--keep-going", "-b", "html",
                    str(source), str(args.output.resolve())], env=env, check=True)


if __name__ == "__main__":
    main()
