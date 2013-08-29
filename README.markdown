# STP

## Authors

* Vijay Ganesh
* Trevor Hansen


## Install

See INSTALL file in the home dir of this program


## Install

See LICENSE file in the home dir of this program


## Website

http://stp.github.io/stp/


## Documentation

https://github.com/stp/stp/wiki/STP-Input-Language


## Papers

Paper on STP Internals:

A Decision Procedure for Bit-Vectors and Arrays by Vijay Ganesh and David L. Dill. In Proceedings of Computer Aided Verification 2007 (CAV 2007), Berlin, Germany, July 2007 ([pdf](http://people.csail.mit.edu/vganesh/Publications_files/vg2007-STP-CAV.pdf)) ([bib](http://people.csail.mit.edu/vganesh/STP_files/STP-ganesh-07.bib))

Paper on EXE Concolic Tester:

EXE: Automatically Generating Inputs of Death by Cristian Cadar, Vijay Ganesh, Peter Pawlowski, Dawson Engler, David Dill. In Proceedings of ACM Conference on Computer and Communications Security 2006 (CCS 2006), Alexandria, Virginia, October, 2006 ([pdf](http://people.csail.mit.edu/vganesh/Publications_files/vg2006-EXE-CCS.pdf)) ([bib](http://people.csail.mit.edu/vganesh/STP_files/EXE-cadarganesh-06.bib))

## Checking Your Installation

```
make check
```


## Regressions

You may need to update the TEST_PREFIX in scripts/Makefile.common, to point to the
directory in which you checked out the test cases. Some test cases have fixed timeouts,
depending on your machine's speed, some test cases may "fail" because they do not 
finish within the timeout. Such timeout failures are unlikely to be a serious problem.

```
make regressall
```
