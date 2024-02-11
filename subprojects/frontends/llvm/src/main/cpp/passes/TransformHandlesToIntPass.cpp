//
// Created by solarowl on 5/10/21.
//

#include "TransformHandlesToIntPass.h"
#include <iostream>

bool TransformHandlesToIntPass::runOnModule(llvm::Module &M) {
    if(M.getFunction("pthread_create")==nullptr) {
        return false;
    } // no pthread create in program

    llvm::Function * pthreadCreate = M.getFunction("pthread_create");
    std::vector<llvm::Type*> pthreadCreateParams;
    for(llvm::Type *type : pthreadCreate->getFunctionType()->params()) {
        pthreadCreateParams.push_back(type);
    }
    pthreadCreateParams.erase(pthreadCreateParams.begin()+1);

    // create thread has 4 parameters, we change the first one to an int
    llvm::FunctionType *thetaCreateThreadType = llvm::FunctionType::get(pthreadCreate->getReturnType(),
                                                                        pthreadCreateParams,
                                                                        false);

    thetaCreateThreadFunction = llvm::Function::Create(thetaCreateThreadType, llvm::Function::ExternalLinkage,
                                                               "theta_pthread_create", M);

    auto &llvmFunctionList = M.getFunctionList();
    for (llvm::Function &llvmFunction : llvmFunctionList) {
        if (!llvmFunction.isDeclaration()) {
            iterateOnFunction(llvmFunction);
        }
    }
    return false;
}


void TransformHandlesToIntPass::iterateOnBasicBlock(llvm::BasicBlock &bb) {
    llvm::Instruction *instruction = bb.getFirstNonPHI();
    while (instruction != nullptr) {
        if (instruction->getOpcode() == llvm::Instruction::Call &&
            instruction->getOperand(instruction->getNumOperands() - 1)->getName().str() == "pthread_create") {
            instruction = handlePthreadCreate(instruction);
        }
        instruction = instruction->getNextNonDebugInstruction();
    }

}

void TransformHandlesToIntPass::iterateOnFunction(llvm::Function &F) {
    // iterate through basic blocks
    llvm::BasicBlock *bb = &F.getEntryBlock();
    while (bb) {
        iterateOnBasicBlock(*bb);
        bb = bb->getNextNode();
    }
}

llvm::Instruction* TransformHandlesToIntPass::handlePthreadCreate(llvm::Instruction *instruction) {
    llvm::BasicBlock &bb = *instruction->getParent();
    std::vector < llvm::Value * > operands = {
        instruction->getOperand(0),
        instruction->getOperand(2),
        instruction->getOperand(3)
    };

    llvm::Instruction *ci = llvm::CallInst::Create(
            thetaCreateThreadFunction->getFunctionType(),
            thetaCreateThreadFunction,
            operands,
            ""
    );
    llvm::BasicBlock::iterator ii(instruction);
    llvm::ReplaceInstWithInst(bb.getInstList(), ii, ci);
    instruction = ci;
    return instruction;
}

llvm::Pass *createTransformHandlesToIntPass() { return new TransformHandlesToIntPass; }
