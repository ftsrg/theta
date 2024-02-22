//
// Created by solarowl on 3/30/21.
//

#ifndef JNI_LIBRARY_GLOBALVARIABLE_H
#define JNI_LIBRARY_GLOBALVARIABLE_H

#include "LlvmImports.h"

#include <iostream>
#include "operands/Register.h"

class GlobalVariable {
private:
    std::string name;
    std::string type;
    std::string initialValue; // e.g. int glob2 = 11 -> i32 11
public:
    GlobalVariable(llvm::GlobalVariable &llvmGlobalVar);

    std::string getName() { return name; }

    std::string getType() { return type; }

    std::string getInitialValue() { return initialValue; }

    void print() {
        std::cout << "GlobalVariable:" << std::endl << "GlobalVar name: " << name << std::endl;
        std::cout << "GlobalVar type: " << type << std::endl;
        std::cout << "GlobalVar initial value: " << initialValue << std::endl;
    }
};


#endif //JNI_LIBRARY_GLOBALVARIABLE_H
