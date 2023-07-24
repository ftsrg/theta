//
// Created by solarowl on 3/30/21.
//

#include "Function.h"

// Function
Function::Function(llvm::Function &llvmFunction) {
    this->name = llvmFunction.getName().str();
    std::string retTypeString;
    llvm::raw_string_ostream ostream(retTypeString);
    llvmFunction.getReturnType()->print(ostream);
    ostream.str();
    this->returnType = retTypeString;

    // parameters
    for (llvm::Value &param : llvmFunction.args()) {
        auto paramRegister = Register::createRegister(param);
        parameters.push_back(paramRegister);
    }

    // basic blocks
    llvm::BasicBlock *llvmBb = &llvmFunction.getEntryBlock();
    while (llvmBb) {
        auto newBasicBlock = std::make_shared<BasicBlock>(*llvmBb);
        BasicBlock::addToLut(llvmBb, newBasicBlock);
        llvmBb = llvmBb->getNextNode();
    }

    // basic blocks
    llvmBb = &llvmFunction.getEntryBlock();
    while (llvmBb) {
        addBasicBlock(*llvmBb);
        llvmBb = llvmBb->getNextNode();
    }
}

void Function::addBasicBlock(llvm::BasicBlock &llvmBasicBlock) {
    // check, if it was already created
    auto bbFromLut = BasicBlock::findBasicBlock(&llvmBasicBlock);
    if (bbFromLut != nullptr) {
        if (!bbFromLut->isInitialized()) bbFromLut->init();
        basicBlocks.push_back(bbFromLut);
    } else {
        auto newBasicBlock = std::make_shared<BasicBlock>(llvmBasicBlock);
        basicBlocks.push_back(newBasicBlock);
        BasicBlock::addToLut(&llvmBasicBlock, newBasicBlock);
        newBasicBlock->init();
    }
}