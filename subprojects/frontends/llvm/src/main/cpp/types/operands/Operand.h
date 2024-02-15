//
// Created by solarowl on 3/30/21.
//

#ifndef JNI_LIBRARY_OPERAND_H
#define JNI_LIBRARY_OPERAND_H

#include "../LlvmImports.h"
#include <iostream>

class Operand {
protected:
    static int nameCounter;
    std::string name;
public:
    virtual std::string getType() = 0;

    virtual std::string getName() { return name; }

    virtual void print() = 0; // for debugging purposes
};

#endif //JNI_LIBRARY_OPERAND_H
