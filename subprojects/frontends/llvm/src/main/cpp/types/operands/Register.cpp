//
// Created by solarowl on 3/30/21.
//

#include "Register.h"

std::unordered_map<llvm::Value *, std::shared_ptr < Register>>
Register::LUT = std::unordered_map < llvm::Value *, std::shared_ptr<Register>>
();

void Register::reset() {
    LUT = std::unordered_map < llvm::Value *, std::shared_ptr<Register>>();
}

Register::Register(llvm::Value &llvmRegister) {
    if(llvmRegister.getName() == "") name = "register_" + std::to_string(nameCounter);
    else {
        name = llvmRegister.getName().str();
        if(name.find("@")==0) { // if it is a pointer to a global var, then it starts with @
            name = name.substr(1); // but we'll remove @
        }
    }
    nameCounter++;
    localVariableName = nullptr;
    std::string typeStr;
    llvm::raw_string_ostream ostream(typeStr);
    llvmRegister.getType()->print(ostream);
    ostream.str();

    this->type = typeStr;

    registerAddress = &llvmRegister;
}

// for global var reg init
Register::Register(llvm::GlobalVariable &globalVariable) {
    localVariableName = nullptr;
    llvm::raw_string_ostream gvTypeStream(this->type);
    globalVariable.getType()->print(gvTypeStream);
    gvTypeStream.str();
    this->name = globalVariable.getName().str();
    this->registerAddress = &globalVariable;
}

void Register::addToLut(std::shared_ptr <Register> newRegister) {
    LUT[newRegister->getRegisterAddress()] = newRegister;
}

std::shared_ptr <Register> Register::createRegister(llvm::Value &llvmRegister) {
    std::shared_ptr <Register> regFromLut = findRegister(&llvmRegister);
    if (regFromLut != nullptr) {
        return regFromLut;
    } else {
        std::shared_ptr <Register> newReg(new Register(llvmRegister));
        addToLut(newReg);
        return newReg;
    }
}

std::shared_ptr <Register> Register::createRegister(llvm::GlobalVariable &globalVariable) {
    std::shared_ptr <Register> regFromLut = findRegister(&globalVariable);
    if (regFromLut != nullptr) {
        return regFromLut;
    } else {
        std::shared_ptr <Register> newReg(new Register(globalVariable));
        addToLut(newReg);
        return newReg;
    }
}

void Register::assignLocalVariable(std::string varName) {
    if (localVariableName != nullptr) {
        std::cout << "Variable " << localVariableName.get() << " was already assigned to register, can't assign "
                  << varName << std::endl;
        return;
    }
    localVariableName = std::unique_ptr<std::string>(new std::string(varName));
    type += " [local]";
}

std::shared_ptr <Register> Register::findRegister(llvm::Value *key) {
    auto it = LUT.find(key);
    if (it == LUT.end()) {
        return nullptr;
    } else {
        return it->second;
    }
}