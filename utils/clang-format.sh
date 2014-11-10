#!/bin/bash

# Format headers and source files but avoid external projects
files="$(find include/ -iname '*.h' -o -iname '*.cpp' | sort)"
files="$files $(find lib/ \( -iname '*.h' -o -iname '*.cpp' \) -not \( -path 'lib/extlib-*' -o -path 'lib/Sat/minisat/*' -o -path 'lib/Sat/cryptominisat2/*' \) | sort )"
files="$files $(find tools/ -iname '*.h' -o -iname '*.cpp' | sort)"
files="$files $(find tests/api \( -iname '*.h' -o -iname '*.cpp' -o -iname '*.c' \) | sort)"
for f in $files; do
    echo "Formating $f"
    clang-format -i -style=file $f
done
