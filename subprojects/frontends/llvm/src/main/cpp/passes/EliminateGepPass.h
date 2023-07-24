//
// Created by solarowl on 4/5/21.
//

#ifndef JNI_LIBRARY_ELIMINATEGEPPASS_H
#define JNI_LIBRARY_ELIMINATEGEPPASS_H

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

#include <string>
#include <iostream>
#include <vector>
#include <unordered_map>

class EliminateGepPass : public llvm::ModulePass {
private:
    bool checkGep(llvm::Instruction* gep);
    llvm::Instruction* handleLoad(llvm::Instruction *instruction);
    llvm::Instruction* handleStore(llvm::Instruction *instruction);

    llvm::Instruction* insertGetArrayElementCall(llvm::Instruction *instruction, llvm::Instruction *gep);
    llvm::Instruction* insertSetArrayElementCall(llvm::Instruction *instruction, llvm::Instruction *gep);

    void iterateOnBasicBlock(llvm::BasicBlock &bb);
    void iterateOnFunction(llvm::Function &F);

    // llvm::Function *setF = nullptr;
    // The return type has to be right and the parameter types should be right, so we may need more than one set/getArrayElement functions
    std::unordered_map<llvm::FunctionType *, llvm::Function *> getElementFunctions;
    std::unordered_map<llvm::FunctionType *, llvm::Function *> setElementFunctions;

    llvm::Function *fetchGetArrayElementFunction(llvm::Type *retType, std::array<llvm::Type*, 2> paramType, llvm::Module &M);
    llvm::Function *fetchSetArrayElementFunction(std::array<llvm::Type*, 3> paramType, llvm::Module &M);

    std::set<llvm::Instruction *> removable;
public:
    char ID;

    EliminateGepPass() : llvm::ModulePass(ID) {}

    bool runOnModule(llvm::Module &M);
};

llvm::Pass *createEliminateGepPass();

#endif //JNI_LIBRARY_ELIMINATEGEPPASS_H
