//
// Created by solarowl on 3/30/21.
//

#include "Module.h"

// Global context
llvm::LLVMContext context;

// Module
Module Module::instance;

bool Module::checkName(llvm::Function &newFunction) {
    std::string newFuncName = newFunction.getName().str();
    for (std::shared_ptr <Function> f : functions) {
        if (f->getName() == newFuncName) {
            return true;
        }
    }
    return false;
}

bool Module::checkName(llvm::GlobalVariable &newGlobalVar) {
    std::string newGlobalVarName = newGlobalVar.getName().str();
    for (std::shared_ptr <GlobalVariable> g : globalVariables) {
        if (g->getName() == newGlobalVarName) {
            return true;
        }
    }
    return false;
}

// Adding function based on the llvm::Function type
void Module::addFunction(llvm::Function &newFunction) {
    if (checkName(newFunction)) {
        std::cout << "Function " << newFunction.getName().str() << "was already added to module!" << std::endl;
    } else {
        functions.push_back(std::make_shared<Function>(newFunction));
    }
    // numOfFunctions++;
}

// Adding global variable based on the llvm::GlobalVariable type
void Module::addGlobalVariable(llvm::GlobalVariable &newGlobalVar) {
    if (checkName(newGlobalVar)) {
        std::cout << "GlobalVariable " << newGlobalVar.getName().str() << "was already added to module!" << std::endl;
    } else {
        globalVariables.push_back(std::make_shared<GlobalVariable>(newGlobalVar));
    }
}


Module::Module() {
    functions = std::vector < std::shared_ptr < Function >> ();
    globalVariables = std::vector < std::shared_ptr < GlobalVariable >> ();
}

void Module::parseLLVMModule(std::shared_ptr <llvm::Module> llvmModule) {
    instance = Module();

    // Analyze module first
    Analysis::checkModule(llvmModule.get());

    auto &globalList = llvmModule->getGlobalList();
    for (llvm::GlobalVariable &globalVar : globalList) {
        addGlobalVariable(globalVar);
    }

    auto &llvmFunctionList = llvmModule->getFunctionList();
    for (llvm::Function &llvmFunction : llvmFunctionList) {
        //if(llvmFunction.getBasicBlockList().size() > 0) {
        if (!llvmFunction.isDeclaration()) {
            addFunction(llvmFunction);
        }
    }
}
