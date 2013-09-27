include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
include_directories(${CMAKE_BINARY_DIR}/src/AST/)

add_library(printer
    AssortedPrinters.cpp
    BenchPrinter.cpp
    CPrinter.cpp
    dotPrinter.cpp
    GDLPrinter.cpp
    LispPrinter.cpp
    PLPrinter.cpp
    SMTLIB1Printer.cpp
    SMTLIB2Printer.cpp
    SMTLIBPrinter.cpp
)
add_dependencies(printer ASTKind_header)