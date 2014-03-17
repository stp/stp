#!/bin/bash

TMPDIR='/tmp/'

skiplist=('')

function usage()
{
    echo "$0 : <path> <solver>"
    echo "looks for .cvc files in <path> recursively and converts them to llvm-lit tests"
    echo "<solver> is used as an oracle for expected test output (sat or unsat)"
}

if [ $# -ne 2 ]; then
    usage
    exit 1
fi

if  [ ! -d $1 ]; then
    echo "$1 is not a directory"
    exit 1
fi

solver="$2"

if which "$solver" ; then
    true # noop
else
    echo "Could not find solver $solver"
    exit 1
fi

for f in $(find "$1" -iname '*.cvc') ; do
    skip=0
    for toskip in ${skiplist[*]}; do
        if [ "$toskip" = "$f" ]; then
            echo "skipping $f"
            skip=1
        fi
    done
    if [ $skip -eq 1 ]; then
        continue
    fi

    # Check if already converted
    firstLine=$(cat "$f" | sed -n '1p')
    if [ $(echo "$firstLine" | grep -Ec '^% RUN:') -eq 1 ]; then
        echo "skipping already converted test"
        continue
    fi

    echo "$f"
    result="$($solver $f)"
    returncode="$?"

    firstline=$( echo "$result" | sed -n '1p')
    modifiedfl="$firstline"

    # Transform output into regex
    if [ $( echo "${firstline}" | grep --ignore-case -c '^invalid') -eq 1 ]; then
        modifiedfl="^[Ii]nvalid"
    elif [ $( echo "${firstline}" | grep --ignore-case -c '^valid') -eq 1 ]; then
        modifiedfl="^[Vv]alid"
    else
        echo "solver output not recognised. skipping"
        continue
    fi


    awkCmd=$( cat <<EOF
BEGIN { print "% RUN: %solver %s | %OutputCheck %s"}
/QUERY/ { print "% CHECK: $modifiedfl"}
{ print }
EOF
    )
    awk "$awkCmd" "$f" > ${TMPDIR}/tempfile
    mv ${TMPDIR}/tempfile "$f"
done
