//
// Created by solarowl on 4/27/21.
//

#ifndef THETA_C_FRONTEND_BRANCHDBGCALLPASS_H
#define THETA_C_FRONTEND_BRANCHDBGCALLPASS_H

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

class BranchDbgCallPass : public llvm::ModulePass {
private:
    llvm::Function *brDbgFunction;
    void handleTerminatorInst(llvm::BasicBlock &bb);
    void iterateOnFunction(llvm::Function &F);
public:
    char ID;

    BranchDbgCallPass() : llvm::ModulePass(ID) {}

    bool runOnModule(llvm::Module &M);
};

llvm::Pass *createBranchDbgCallPass();

#endif //THETA_C_FRONTEND_BRANCHDBGCALLPASS_H
