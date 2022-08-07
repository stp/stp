#!/bin/bash     

#Each input should be simplified down to either true or false.
#We no longer generate a CNF for trivially true/false instances,
#so there should be no CNF generated for these.


rm -f output_*.cnf

files=$(ls -1 -S *.smt2 *.smt)
for f in $files; do
	echo $f
	stp --output-CNF $f
	if [ -e output_0.cnf ] ; then
		echo --fail $f
		exit 10
	fi

done

