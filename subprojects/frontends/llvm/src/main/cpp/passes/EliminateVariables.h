#ifndef JNI_LIBRARY_ELIMINATEVARIABLES_H
#define JNI_LIBRARY_ELIMINATEVARIABLES_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Pass.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <vector>

class EliminateVariables : public llvm::FunctionPass {
    char ID;
public:
    EliminateVariables()
            : llvm::FunctionPass(ID) {}

    virtual bool runOnFunction(llvm::Function &f);
};

llvm::Pass *createEliminationPass();

#endif