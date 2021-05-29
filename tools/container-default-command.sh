#!/usr/bin/env bash
#
# Copyright Norbert Manthey, 2019

# This script is executed as default in the container

set -x

echo "Start container default command"
echo "Start container default command" 1>&2

# Default location is defined by environment variable INPUT_FILE
INPUT_FILE=${INPUT_FILE:-}


# Get file from S3, copy it to a temporary directory
trap '[ -d "$STPTMPDIR" ] && rm -rf "$STPTMPDIR"' EXIT
STPTMPDIR=$(mktemp -d)

SCRIPT=$(readlink -e "$0")
SCRIPTDIR=$(dirname "$SCRIPT")


# In case that variable is not given, we might have a file stored in S3
if [ -z "$INPUT_FILE" ]
then
    if ! command -v aws &> /dev/null
    then
        echo "error: cannot find tool 'aws', abort" 1>&2
        exit 1
    fi
    
    # Get file basename
    PROBLEM=$(basename ${COMP_S3_PROBLEM_PATH})
    
    echo "Trying to obtain the file from S3: ${S3_BKT}/${COMP_S3_PROBLEM_PATH}" 1>&2
    aws s3 cp s3://"${S3_BKT}"/"${COMP_S3_PROBLEM_PATH}" "$STPTMPDIR/$PROBLEM"
    
    INPUT_FILE="$STPTMPDIR/$PROBLEM"
fi


# Final check wrt input file
if [ ! -r "$INPUT_FILE" ]
then
    echo "error: cannot read input file '$INPUT_FILE'" 1>&2
    exit 1
fi

# Capture stdin to file, in case we miss an input file
if [ -z "$INPUT_FILE" ]; then
    # Get file from stdin, so that we can forward the file
    INPUT_FILE="$STPTMPDIR"/stdin.smt2
    echo "Catch file from stdin in $INPUT_FILE (as none was specified) ..." 1>&2
    cat > "$INPUT_FILE"
fi

# Run starexec portfolio script on input file
starexec_run_portfolio "$INPUT_FILE"

# Using native solver, use the next command:
# echo "Run stp with file $INPUT_FILE" 1>&2
# exec /usr/local/bin/stp --SMTLIB2 "$INPUT_FILE"
