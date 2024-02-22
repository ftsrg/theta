//
// Created by solarowl on 3/30/21.
//

#ifndef JNI_LIBRARY_MODULE_H
#define JNI_LIBRARY_MODULE_H

#include "LlvmImports.h"

#include <iostream>
#include "Function.h"
#include "BasicBlock.h"
#include "operands/Register.h"
#include "../utilities/Analysis.h"
#include "GlobalVariable.h"

// Global context
extern llvm::LLVMContext context;

class Module { // Singleton
private:
    std::vector <std::shared_ptr<Function>> functions;
    std::vector <std::shared_ptr<GlobalVariable>> globalVariables;

    bool checkName(llvm::Function &newFunction);

    bool checkName(llvm::GlobalVariable &newGlobalVar);

    // Adding function based on the llvm::Function type
    void addFunction(llvm::Function &newFunction);

    void addGlobalVariable(llvm::GlobalVariable &newGlobalVar);

    Module();

    static Module instance;
public:
    static Module &getModule() {
        return instance;
    }

    void parseLLVMModule(std::shared_ptr <llvm::Module> llvmModule);

    int getNumOfFunctions() { return functions.size(); }

    int getNumOfGlobalVariables() { return globalVariables.size(); }

    std::shared_ptr <Function> getFunction(int functionIndex) { return functions[functionIndex]; }

    int findFunctionByName(std::string functionName) { // Find the index of the function given with functionName
        auto it = std::find_if(std::begin(functions), std::end(functions),
                               [&](std::shared_ptr <Function> const &f) { return f->getName() == functionName; });
        if (it == std::end(functions)) {
            return -1;
        } else return it - functions.begin();
    }

    std::shared_ptr <GlobalVariable> getGlobalVariable(int gvIndex) { return globalVariables[gvIndex]; }

    void print() {
        std::cout << "Module, numOfFunctions: " << functions.size() << ", functions: ";
        for (auto func : functions) {
            func->print();
        }
        std::cout << ", global variables: " << std::endl;
        for (auto gv : globalVariables) {
            gv->print();
        }
        std::cout << std::endl;
    }
};


#endif //JNI_LIBRARY_MODULE_H
