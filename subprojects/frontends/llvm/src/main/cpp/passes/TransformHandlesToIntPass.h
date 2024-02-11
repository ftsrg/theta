//
// Created by solarowl on 5/10/21.
//

#ifndef THETA_C_FRONTEND_TRANSFORMHANDLESTOINT_H
#define THETA_C_FRONTEND_TRANSFORMHANDLESTOINT_H

// TODO superfluous imports
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Pass.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstrTypes.h"
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <vector>

class TransformHandlesToIntPass : public llvm::ModulePass {
private:
    llvm::Function * thetaCreateThreadFunction;

    llvm::FunctionType *mutatedType;
    llvm::Instruction* handlePthreadCreate(llvm::Instruction *instruction);

    void iterateOnBasicBlock(llvm::BasicBlock &bb);
    void iterateOnFunction(llvm::Function &F);
public:
    char ID;

    TransformHandlesToIntPass() : llvm::ModulePass(ID) {}

    bool runOnModule(llvm::Module &M);

};

llvm::Pass *createTransformHandlesToIntPass();

// pthread_create

#endif //THETA_C_FRONTEND_TRANSFORMHANDLESTOINT_H
