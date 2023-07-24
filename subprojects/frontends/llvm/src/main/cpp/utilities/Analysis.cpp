//
// Created by solarowl on 4/19/21.
//

#include "Analysis.h"

bool Analysis::hasIntInBitwiseBinaryOp = false;
bool Analysis::hasStructs = false;

void Analysis::checkInstruction(llvm::Instruction* instruction) {
    checkIfIntInBitwiseBinary(instruction);
}

void Analysis::checkModule(const llvm::Module* module) {
    checkIfHasStructs(module);
}

void Analysis::checkIfHasStructs(const llvm::Module* module) {
    llvm::TypeFinder StructTypes;
    StructTypes.run(*module, true); // TODO we do not check for opaque struct - we do not handle them yet

    if(StructTypes.begin()!=StructTypes.end()) {
        // std::cout << "there are structs" << std::endl;
        hasStructs = true;
    }

    // debug print of struct types
    // for (auto *STy : StructTypes)
    //    STy->print(llvm::errs());
}

// TODO refactor this to smaller pieces
void Analysis::checkIfIntInBitwiseBinary(llvm::Instruction* instruction) {
    // Analyzing so we can set hasIntInBitwiseBinaryOp accordingly
    llvm::BinaryOperator *binOp = llvm::dyn_cast<llvm::BinaryOperator>(instruction);
    // 1. if the flag is already true, the test is superfluous
    // 2. is it a binOp?
    // 3. is it a bitwise binop?
    // so we only want to check the bitwise binary instructions any further
    // because we want to check if there are any bitwise binary ops, that has non-booleans (i1) integers
    // (example: | (bitwise or -> need integers) vs || (logical or, works with bools)
    if(!hasIntInBitwiseBinaryOp && binOp != nullptr) {
        // if it is one of and,or,xor and is only used by icmp 0 compares, then int arith is still alright
        if(checkIfAndOrXor(binOp)) {
            // all operands should be of the same type, according to llvm ref manual, so we only need to check one
            llvm::IntegerType *intType = llvm::dyn_cast<llvm::IntegerType>(binOp->getOperand(0)->getType());
            if (intType != nullptr && intType->getBitWidth() > 1) {
                // if it is an integer, we need to check, if it is only used by icmps, comparing them to zero values
                // (the optimizations, mainly CFG simplifications, can create i32 binary ops with icmps from logical ops)
                // (but if the bitwise op is only used by icmps, we can handle that alright)

                // I left the debugging prints in there, as they can be useful - at some point we should probably delete them
                bool icmpOnly = true;
                llvm::ICmpInst *icmp;
                for (auto user : instruction->users()) {
                    if ((icmp = llvm::dyn_cast<llvm::ICmpInst>(user)) != nullptr) {
                        llvm::Constant *constCmpOperand = llvm::dyn_cast<llvm::Constant>(icmp->getOperand(1));
                        if (constCmpOperand != nullptr && constCmpOperand->isZeroValue()) {
                            // std::cout << "icmp :)" << std::endl;
                        } else {
                            // std::cout << "not icmp :c" << std::endl;
                            icmpOnly = false;
                        }
                    } else {
                        // std::cout << "not icmp :c" << std::endl;
                        icmpOnly = false;
                    }
                }

                if (!icmpOnly) {
                    hasIntInBitwiseBinaryOp = true;
                    // std::cout << "Found one!" << std::endl;
                    binOp->print(llvm::errs());
                }
            }
        } else if(checkIfShift(binOp)) { // in this case, on the other hand, shifts on integers will always need integer arithmetics
            llvm::IntegerType *intType = llvm::dyn_cast<llvm::IntegerType>(binOp->getOperand(0)->getType());
            if (intType != nullptr && intType->getBitWidth() > 1) {
                hasIntInBitwiseBinaryOp = true;
            }
        }
    }
}

bool Analysis::checkIfShift(const llvm::BinaryOperator *binOp) {
    std::string opname = binOp->getOpcodeName();
    if(opname=="shl") return true;
    if(opname=="lshr") return true;
    if(opname=="ashr") return true;
    return false;
}

bool Analysis::checkIfAndOrXor(const llvm::BinaryOperator *binOp) {
    std::string opname = binOp->getOpcodeName();
    if(opname=="and") return true;
    if(opname=="or") return true;
    if(opname=="xor") return true;
    return false;
}

void Analysis::reset() {
    hasIntInBitwiseBinaryOp = false;
    hasStructs = false;
}
