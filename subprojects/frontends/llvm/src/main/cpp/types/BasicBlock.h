//
// Created by solarowl on 3/30/21.
//

#ifndef JNI_LIBRARY_BASICBLOCK_H
#define JNI_LIBRARY_BASICBLOCK_H

#include "LlvmImports.h"

#include <unordered_map>
#include <iostream>
#include "Instruction.h"

class BasicBlock {
private:
    bool initialized = false;
    std::string name; // if unnamed, a generated (block_x) name is generated
    int numOfInstructions;
    std::vector <std::shared_ptr<Instruction>> instructions;
    llvm::BasicBlock &basicBlock;
    static int nameCounter;
    static std::unordered_map<llvm::BasicBlock *, std::shared_ptr < BasicBlock>> LUT;

public:
    BasicBlock(llvm::BasicBlock &basicBlock) : basicBlock(basicBlock) {
        std::string bbName = basicBlock.getName().str();
        if (bbName == "") {
            this->name = "block_" + std::to_string(nameCounter);
            nameCounter++;
        } else {
            this->name = bbName;
        }
    }

    static void reset();

    void init();

    int getNumOfInstructions() { return numOfInstructions; }

    std::string getName() { return name; }

    std::shared_ptr <Instruction> getInstruction(int i) { return instructions[i]; }

    bool isInitialized() { return initialized; }

    void print() {
        std::cout << "BasicBlock, name: " << name << ", numOfInstructions: " << numOfInstructions << ", instructions: "
                  << std::endl;
        for (auto inst : instructions) { inst->print(); }
        std::cout << std::endl;
    }

    static std::shared_ptr <BasicBlock> findBasicBlock(llvm::BasicBlock *key);

    static void addToLut(llvm::BasicBlock *bbPtr, std::shared_ptr <BasicBlock> basicBlock);
};


#endif //JNI_LIBRARY_BASICBLOCK_H
