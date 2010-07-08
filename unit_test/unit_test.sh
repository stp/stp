#!/bin/bash     

#Each file should be simplified down to either true or false, so the CNF generated should
#be very small if simplifications are working as they should.

rm -f output_*.cnf

files=`ls -1 -S *.smt2`
for f in $files; do
	stp --output-CNF $f
	cnf=`cat output_*.cnf  | grep -v "^c" | grep -v "^$" |  wc -l`
	if [ $cnf -gt 3 ] ; then
		echo --fail
		exit 10
	fi

done

