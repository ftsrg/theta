//
// Created by solarowl on 3/30/21.
//

#include "GlobalVariable.h"

// GlobalVariable
GlobalVariable::GlobalVariable(llvm::GlobalVariable &llvmGlobalVar) {
    this->name = llvmGlobalVar.getName().str();

    llvm::raw_string_ostream ostream(type);
    llvmGlobalVar.getValueType()->print(ostream);
    ostream.str();

    llvm::raw_string_ostream ostream2(initialValue);
    llvmGlobalVar.getInitializer()->print(ostream2);
    ostream2.str();

    auto gvPointerRegister = Register::createRegister(llvmGlobalVar);
}