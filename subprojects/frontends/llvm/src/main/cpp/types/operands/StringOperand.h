//
// Created by solarowl on 4/11/21.
//

#ifndef JNI_LIBRARY_FUNCTIONLABEL_H
#define JNI_LIBRARY_FUNCTIONLABEL_H

#include "Operand.h"

class StringOperand : public Operand {
public:
    std::string getType() override { return "constant"; }

    StringOperand(std::string opName);

    void print() override { std::cout << "StringOperand, name: " << name << std::endl; }

};


#endif //JNI_LIBRARY_FUNCTIONLABEL_H
