//
// Created by solarowl on 4/19/21.
//

#ifndef THETA_C_FRONTEND_ANALYSIS_H
#define THETA_C_FRONTEND_ANALYSIS_H

#include "../types/LlvmImports.h"
#include "llvm/IR/TypeFinder.h"
#include <iostream>

class Analysis {
private:
    // hasIntInBitwiseBinaryOp:
    // we need to know, if in Theta we should use bitwise or integer arithmetic
    // if there are bitwise binary ops (with a few exceptions, see in checkIfIntInBitwiseBinary)
    // with integer operands, than we have to use bitwise arithmetic
    // otherwise we can use integer arithmetics which is faster
    static bool hasIntInBitwiseBinaryOp;
    static bool checkIfShift(const llvm::BinaryOperator *binOp);
    static bool checkIfAndOrXor(const llvm::BinaryOperator *binOp);
    static void checkIfIntInBitwiseBinary(llvm::Instruction *instruction);

    static bool hasStructs;
    static void checkIfHasStructs(const llvm::Module*);
public:
    static void checkInstruction(llvm::Instruction* instruction); // when parsing, every instruction should be checked with this
    static void checkModule(const llvm::Module*); // before parsing module, this should be called on it
    static void reset();

    static bool getStructAnalysisResult() {
        return hasStructs;
    }
    static bool getBitwiseOpAnalysisResult() {
        return hasIntInBitwiseBinaryOp;
    }
};


#endif //THETA_C_FRONTEND_ANALYSIS_H
