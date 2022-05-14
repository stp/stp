The src/ directory is organized into subdirectories for each distinct component of STP.

* `absrefine_counterexample`: Functions related to abstraction refinement and counterexample construction.
* `AST`: Implements the abstract syntax tree for parsed solver inputs.
* `c_interface`: Defines a C interface for parsing input files, constructing expressions, executing queries, etc.
* `cpp_interface`: Defines the C++ interface for invoking STP.
* `extlib-abc`: The [ABC](http://www.eecs.berkeley.edu/~alanmi/abc/abc.htm) package.
* `extlib-constbv`:  A library that implements multi-word fixed-length integers, based on Steffen Beyer's [Bit::Vector](http://guest.engelschall.com/~sb/download/) perl module.
* `main`: Implements the executable tool `stp`
* `parser`: Contains the parsers for the CVC, SMT-LIB1, and SMT-LIB2 input formats.
* `printer`:  Implements various output formatters.
* `Sat`: This is a copy of [MiniSat](http://minisat.se), with [CryptoMiniSat](http://www.msoos.org/cryptominisat2/) and some other files added.
* `simplifier`: Simplification algorithms for the AST
* `STPManager`: Class that hold all the components together
* `to-sat`: Conversion of AST to SAT
* `util`: Handy utilities for smaller tasks