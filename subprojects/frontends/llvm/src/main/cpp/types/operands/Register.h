//
// Created by solarowl on 3/30/21.
//

#ifndef JNI_LIBRARY_REGISTER_H
#define JNI_LIBRARY_REGISTER_H

#include "../LlvmImports.h"

#include <unordered_map>
#include <iostream>
#include "Operand.h"

class Register : public Operand {
    std::unique_ptr <std::string> localVariableName; // TODO should be optional instead of u_ptr?
    llvm::Value *registerAddress;
    std::string type;
    // llvm::Type* type; // TODO could be a string only?

    static std::unordered_map<llvm::Value *, std::shared_ptr < Register>> LUT;

    Register(llvm::Value &llvmRegister);

    Register(llvm::GlobalVariable &globalVariable);

    static void addToLut(std::shared_ptr <Register> newRegister);

public:
    static std::shared_ptr <Register>
    createRegister(llvm::Value &llvmRegister); // creates the register and adds it to LUT / finds it in LUT
    static std::shared_ptr <Register> createRegister(llvm::GlobalVariable &globalVariable);

    void assignLocalVariable(std::string varName);
    std::string getLocalVariableName() {
        if(localVariableName==nullptr) {
            return "";
        } else {
            return *localVariableName;
        }
    }

    std::string getName() override {
        // if the register has a local var name assigned,
        // we return that, instead of the generated name
        if(localVariableName != nullptr) {
            return *localVariableName;
        } else {
            return name;
        }
    }

    llvm::Value *getRegisterAddress() { return registerAddress; }

    std::string getType() override { return type; }

    void print() override {
        std::cout << "Register, name: " << name << ", RegisterAddress: " << registerAddress;
        std::cout << ", type: " << getType();
        if (localVariableName != nullptr) std::cout << ", LocalVarName: " << *localVariableName;
        std::cout << std::endl;
    }

    static void printLUT() {
        std::cout << "Register LUT content: " << std::endl;
        for (auto &it: LUT) {
            it.second->print();
        }
    }

    static void reset();
    
    static std::shared_ptr <Register> findRegister(llvm::Value *key);
};

#endif //JNI_LIBRARY_REGISTER_H
