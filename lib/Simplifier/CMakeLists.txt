add_library(simplifier OBJECT
    bvsolver.cpp
    consteval.cpp
    MutableASTNode.cpp
    PropagateEqualities.cpp
    RemoveUnconstrained.cpp
    simplifier.cpp
    SubstitutionMap.cpp
    VariablesInExpression.cpp

    constantBitP/ConstantBitP_Arithmetic.cpp
    constantBitP/ConstantBitP_Boolean.cpp
    constantBitP/ConstantBitP_Comparison.cpp
    constantBitP/ConstantBitP_Division.cpp
    constantBitP/ConstantBitP_MaxPrecision.cpp
    constantBitP/ConstantBitP_Multiplication.cpp
    constantBitP/ConstantBitPropagation.cpp
    constantBitP/ConstantBitP_Shifting.cpp
    constantBitP/ConstantBitP_TransferFunctions.cpp
    constantBitP/ConstantBitP_Utility.cpp
    constantBitP/FixedBits.cpp
)
add_dependencies(simplifier ASTKind_header)
