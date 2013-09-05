include_directories(${CMAKE_CURRENT_BINARY_DIR}/../AST/)
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