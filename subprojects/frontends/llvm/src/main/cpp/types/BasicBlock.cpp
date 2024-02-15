//
// Created by solarowl on 3/30/21.
//

#include "BasicBlock.h"

// BasicBlock
int BasicBlock::nameCounter = 0;
std::unordered_map<llvm::BasicBlock *, std::shared_ptr < BasicBlock>>
BasicBlock::LUT = std::unordered_map < llvm::BasicBlock *, std::shared_ptr<BasicBlock>>
();

void BasicBlock::reset() {
    LUT = std::unordered_map < llvm::BasicBlock *, std::shared_ptr<BasicBlock>>();
}

void BasicBlock::init() {
    initialized = true;
    numOfInstructions = 0;

    instructions = std::vector < std::shared_ptr < Instruction >> ();
    for (llvm::Instruction &inst : basicBlock.getInstList()) { // TODO not the nicest if-else tree in the world - restructure, when refactoring
        if (inst.getOpcode() == llvm::Instruction::Call &&
            inst.getOperand(inst.getNumOperands() - 1)->getName().str() == "llvm.dbg.declare") {
            // special case - llvm.dbg.declare call, we handle the info in it here and won't create an Instruction from it
            // Instruction::handleLlvmDbgDeclare(inst);
        } else if (inst.getOpcode() == llvm::Instruction::Call &&
                   inst.getOperand(inst.getNumOperands() - 1)->getName().str() == "llvm.dbg.value") {
            // Instruction::handleLlvmDbgValue(inst);
            // ignore these
        } else if (inst.getOpcode() == llvm::Instruction::Call &&
                   inst.getOperand(inst.getNumOperands() - 1)->getName().str() == "llvm.dbg.label") {
            // we'll ignore these for now - if we'll ever need this, we'll get the label name out somehow here
        } else {
            instructions.push_back(std::make_shared<Instruction>(inst));
            numOfInstructions++; // easiest way to get this info seems to be counting them
        }
    }
}

void BasicBlock::addToLut(llvm::BasicBlock *bbPtr, std::shared_ptr <BasicBlock> basicBlock) {
    LUT[bbPtr] = basicBlock;
}

std::shared_ptr <BasicBlock> BasicBlock::findBasicBlock(llvm::BasicBlock *key) {
    auto it = LUT.find(key);
    if (it == LUT.end()) {
        return nullptr;
    } else {
        return it->second;
    }
}