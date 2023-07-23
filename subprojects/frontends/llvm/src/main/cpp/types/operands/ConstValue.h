//
// Created by solarowl on 3/30/21.
//

#ifndef JNI_LIBRARY_CONSTVALUE_H
#define JNI_LIBRARY_CONSTVALUE_H

#include "../LlvmImports.h"
#include <iostream>
#include "Operand.h"

class ConstValue : public Operand {
    // name is e.g. "i32 2"
public:
    std::string getType() override { return "constant"; }

    ConstValue(llvm::Value &llvmConstValue);

    void print() override { std::cout << "Constant, name: " << name << std::endl; }
};


#endif //JNI_LIBRARY_CONSTVALUE_H
