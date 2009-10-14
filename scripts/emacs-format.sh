 #!/bin/sh

 # File: my-indent Opens a set of files in emacs and executes the
 # emacs-format-function.  Assumes the function named
 # emacs-format-function is defined in the file named
 # emacs-format-file.

 loadpath=`pwd`
 if [ $# == 0 ]
 then
    echo "my-indent requires at least one argument." 1>&2
       echo "Usage: my-indent files-to-indent" 1>&2
	  exit 1
 fi

 while [ $# -ge 1 ]
 do
  if [ -d $1 ]
  then
    echo "Argument of my-indent $1 cannot be a directory." 1>&2
    exit 1
  fi

  # Check for existence of file:
  ls $1 2> /dev/null | grep $1 > /dev/null
  if [ $? != 0 ]
  then
    echo "my-indent: $1 not found." 1>&2
    exit 1
  fi
  echo "Indenting $1 with emacs in batch mode"
  emacs -batch $1 -l $loadpath/scripts/emacs-format-file -f emacs-format-function
  echo
  shift 1
 done
 exit 0

