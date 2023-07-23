//
// Created by solarowl on 4/5/21.
//

#ifndef JNI_LIBRARY_TOPOSORTPASS_H
#define JNI_LIBRARY_TOPOSORTPASS_H

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

// Sorts the blocks in strongly connected components based on topological order
// Basic block loops need to have an entry block (to the loop), but if this block isn't
// the first in the IR, we have the potential problem, that when iterating through the blocks,
// we find a register on a (non-phi node) instruction's right hand side, which isn't assigned yet.
// (Of course we won't run into this, when running the IR, but it's problematic, when we are transforming it into an XCFA)
// This pass eliminates the above given possibility
class ToposortPass : public llvm::FunctionPass {
    char ID;
public:
    ToposortPass()
            : llvm::FunctionPass(ID) {}

    virtual bool runOnFunction(llvm::Function &f);
};

llvm::Pass *createToposortPass();

#endif //JNI_LIBRARY_TOPOSORTPASS_H
