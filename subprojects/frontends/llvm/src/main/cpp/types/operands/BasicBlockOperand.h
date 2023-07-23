//
// Created by solarowl on 4/11/21.
//

#ifndef JNI_LIBRARY_BASICBLOCKLABEL_H
#define JNI_LIBRARY_BASICBLOCKLABEL_H

#include "Operand.h"

class BasicBlockOperand : public Operand {
public:
    std::string getType() override { return "constant"; }

    BasicBlockOperand(std::string _name);

    void print() override { std::cout << "BasicBlockOperand, name: " << name << std::endl; }

};


#endif //JNI_LIBRARY_BASICBLOCKLABEL_H
