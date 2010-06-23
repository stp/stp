#!/bin/bash     

#Each file should be simplified down to either true or false, so the CNF generated should
#be very small if simplifications are working as they should.

rm output_*.cnf

files=`ls -1 -S *.smt2`
for f in $files; do
	stp --simplifying-minisat --output-CNF $f
	cnf=`cat output_*.cnf  | wc -l`
	if [ $cnf -gt 3 ] ; then
		exit 10
	fi

done

