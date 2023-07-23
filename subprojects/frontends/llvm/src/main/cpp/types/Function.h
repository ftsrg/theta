//
// Created by solarowl on 3/30/21.
//

#ifndef JNI_LIBRARY_FUNCTION_H
#define JNI_LIBRARY_FUNCTION_H

#include "LlvmImports.h"

#include <iostream>
#include "BasicBlock.h"

// Format: Tuple3<Name, RetType, Tuple2<Type, Name>[0..*]>
class Function {
private:
    std::string name;
    std::string returnType;
    std::vector <std::shared_ptr<Register>> parameters;

    std::vector <std::shared_ptr<BasicBlock>> basicBlocks;
public:
    Function(llvm::Function &newFunction);

    void addBasicBlock(llvm::BasicBlock &llvmBasicBlock);

    std::string getName() { return name; }

    std::string getReturnType() { return returnType; }

    int getNumOfParameters() { return parameters.size(); }

    std::shared_ptr <Register> getParameter(int paramIndex) { return parameters[paramIndex]; }

    int getNumOfBasicBlocks() { return basicBlocks.size(); }

    std::shared_ptr <BasicBlock> getBasicBlock(int basicBlockIndex) { return basicBlocks[basicBlockIndex]; }

    int findBasicBlockByName(std::string basicBlockName) { // Find the index of the function given with functionName
        auto it = std::find_if(std::begin(basicBlocks), std::end(basicBlocks),
                               [&](std::shared_ptr <BasicBlock> const &b) { return b->getName() == basicBlockName; });
        if (it == std::end(basicBlocks)) {
            return -1;
        } else return it - basicBlocks.begin();
    }

    void print() {
        std::cout << "Function, name: " << name << ", returnType: " << returnType << ", Parameters: " << std::endl;
        for (auto param : parameters) {
            param->print();
        }
        std::cout << ", BasicBlocks: ";
        for (auto bb : basicBlocks) {
            bb->print();
        }
        std::cout << std::endl;
    }
};


#endif //JNI_LIBRARY_FUNCTION_H
