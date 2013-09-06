#!/bin/bash

# Generate a string describing the current commit

# Try git describe first. This will only work if a tag already exists!
STR=$( git describe --tags 2> /dev/null)

# If that didn't work just use the commit hash
if [ $? -ne 0 ]; then
  STR=$( git rev-parse HEAD)
fi

echo $STR
