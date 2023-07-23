//
// Created by solarowl on 3/30/21.
//

#ifndef JNI_LIBRARY_INSTRUCTION_H
#define JNI_LIBRARY_INSTRUCTION_H

#include <iostream>

#include "LlvmImports.h"
#include "operands/Register.h"
#include "operands/Operand.h"
#include "operands/ConstValue.h"
#include "operands/BasicBlockOperand.h"
#include "operands/StringOperand.h"
#include "../utilities/Analysis.h"

// Format: Tuple4<Opcode, RetVar, Tuple2<VarType, Name>[0..*], lineNumber>
class Instruction {
private:
    unsigned int opcode; // llvm opcode
    std::string opname;
    std::vector <std::shared_ptr<Operand>> operands;
    std::shared_ptr <Register> retVariable; // some operations have one, some don't
    int lineNumber;

    bool handlePhiNode(llvm::Instruction &inst);
    bool handleCmp(llvm::Instruction &inst);
    bool handleConditionalBr(llvm::Instruction &br);
    bool handleOrderingString(llvm::Instruction &inst);

    class OperandHandler {
    public:
        bool handleInstruction(llvm::Value *operand, Instruction &inst);

        bool handleBasicBlock(llvm::Value *operand, Instruction &inst);

        bool handleFunction(llvm::Value *operand, Instruction &inst);

        bool handleConstant(llvm::Value *operand, Instruction &inst);

        bool handleFunctionArgument(llvm::Value *operand, Instruction &inst);
    };

public:
    Instruction(llvm::Instruction &inst);

    void print() {
        std::cout << "Instruction " << opname << ", opcode: " << opcode << " lineNumber: " << lineNumber
                  << ", retVariable: ";
        if (retVariable)retVariable->print();
        std::cout << ", Operands: " << std::endl;
        for (auto op : operands) { op->print(); }
        std::cout << std::endl;
    }

    int getNumOfOperands() { return operands.size(); }

    int getOpcode() { return opcode; }

    std::string getOpname() { return opname; }

    int getLineNumber() { return lineNumber; }

    std::shared_ptr <Register> getRetVariable() { return retVariable; }

    std::shared_ptr <Operand> getOperand(int operandIndex) { return operands[operandIndex]; }

    void changeOperand(int operandIndex,
                       ConstValue operand); // Copies the operand to the given index in operands, used to change gazer's metadata call's operands

    static void handleLlvmDbgDeclare(llvm::Instruction &call);
    static void handleLlvmDbgValue(llvm::Instruction &call);
};

#endif //JNI_LIBRARY_INSTRUCTION_H
