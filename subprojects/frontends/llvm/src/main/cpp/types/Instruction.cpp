//
// Created by solarowl on 3/30/21.
//

#include "Instruction.h"
#include "BasicBlock.h" // needs to be here due to dependency cycle
#include <llvm/Support/raw_ostream.h>

// Instruction
Instruction::Instruction(llvm::Instruction &inst) {
    // a bit of analysis first
    Analysis::checkInstruction(&inst);

    // opcode
    opcode = inst.getOpcode();

    // opname
    opname = inst.getOpcodeName();
    // How to get name of opcode: std::cout<<"Haliho "<<inst.getOpcodeName()<<std::endl;

    // retvar
    if (inst.getType()->getTypeID() != llvm::Type::VoidTyID) {    // Not void type
        retVariable = Register::createRegister(llvm::cast<llvm::Value>(inst));
    } else {
        retVariable = nullptr;
    }

    // line number
    lineNumber = -1;
    auto &location = inst.getDebugLoc();
    if (location) {
        lineNumber = location.getLine();
    }

    // if it is a load or store, add metadata about atomicity
    handleOrderingString(inst);
    // handle icmp/fcmp and PHI node (it is not part of operandHandler, as it is a special instruction, not an operand
    handleCmp(inst);
    if (handlePhiNode(inst)) {
        return;
    }
    if(handleConditionalBr(inst)) {
        return;
    }

    // operands
    for (unsigned int i = 0; i < inst.getNumOperands(); i++) {
        llvm::Value *operand = inst.getOperand(i);

        OperandHandler oph{};
        // "cheap/simple" chain of responsibility
        if (oph.handleInstruction(operand, *this));
        else if (oph.handleBasicBlock(operand, *this));
        else if (oph.handleFunction(operand, *this));
        else if (oph.handleConstant(operand, *this));
        else if (oph.handleFunctionArgument(operand, *this));
        else {
            // Operand type unknown - so it's an error
            std::cerr << "Unknown value type as right hand operand in instruction!" << std::endl;
            std::cerr << "Register LUT: ";
            Register::printLUT();
            std::cerr << "Pointer: " << operand << std::endl;
            operand->print(llvm::errs());
            std::cout << std::endl;
            std::cerr << "Instruction: " << std::endl;
            inst.print(llvm::errs());
            std::cerr << std::endl;
            abort();
        }

    }

}

bool Instruction::handleConditionalBr(llvm::Instruction &br) {
    if((std::string)(br.getOpcodeName())=="br" && br.getNumOperands()==3) {
        OperandHandler oph{};

        if (oph.handleInstruction(br.getOperand(0), *this));
        else if (oph.handleConstant(br.getOperand(0), *this));

        oph.handleBasicBlock(br.getOperand(2), *this);
        oph.handleBasicBlock(br.getOperand(1), *this);
        return true;
    } else {
        return false;
    }
}

void Instruction::handleLlvmDbgValue(llvm::Instruction &call) {
    handleLlvmDbgDeclare(call); // works the same way
}

void Instruction::handleLlvmDbgDeclare(llvm::Instruction &call) {
    llvm::Value *var = call.getOperand(
            1); // operand 1 is the metadata with the local variable name (the name from the C code)
    llvm::Value *_register = call.getOperand(0); // operand 0 is the metadata with the Register

    llvm::DILocalVariable *metaVarName = llvm::dyn_cast<llvm::DILocalVariable>(llvm::dyn_cast<llvm::MetadataAsValue>(
            var)->getMetadata()); // cast it from value to metadata with the wrapper & get the metadata out

    llvm::Metadata *registerMetadata = llvm::dyn_cast<llvm::MetadataAsValue>(_register)->getMetadata();
    llvm::LocalAsMetadata *metaRegister = llvm::dyn_cast<llvm::LocalAsMetadata>(
            registerMetadata); // cast it from value to metadata with the wrapper & get the metadata out

    std::shared_ptr <Register> registerFromMetadata = nullptr;
    if (metaRegister != nullptr) {
        registerFromMetadata = Register::findRegister(metaRegister->getValue());
    }
    // in theory, we probably won't have both a dbg declare and value call, but we'll check none the less, if loc var name wasn't assigned already
    if (registerFromMetadata != nullptr && registerFromMetadata->getLocalVariableName()=="" ) {
        registerFromMetadata->assignLocalVariable(metaVarName->getName().str());
    } else {
        // std::cout << "Warning: Register in llvm.dbg.declare/.value metadata not found!" << std::endl;
        // not an error, the register is probably an undef, we just won't use it
    }
}

void
Instruction::changeOperand(int operandIndex, ConstValue operand) { // Copies the operand to the given index in operands
    operands[operandIndex] = std::make_shared<ConstValue>(operand);
}

bool Instruction::handleCmp(llvm::Instruction &inst) {
    if (opcode == llvm::Instruction::ICmp || opcode == llvm::Instruction::FCmp) {
        llvm::CmpInst *cmpInst = llvm::dyn_cast<llvm::CmpInst>(&inst);
        operands.push_back(std::make_shared<StringOperand>(
                llvm::CmpInst::getPredicateName(cmpInst->getPredicate()).str()));
        return true;
    } else {
        return false;
    }
}

bool Instruction::handlePhiNode(llvm::Instruction &inst) {
    if (opcode == llvm::Instruction::PHI) {
        llvm::PHINode *phiNode = llvm::dyn_cast<llvm::PHINode>(&inst);
        unsigned int numParams = phiNode->getNumIncomingValues();
        for (unsigned int i = 0; i < numParams; ++i) {
            llvm::Value *value = phiNode->getIncomingValue(i);
            llvm::BasicBlock *block = phiNode->getIncomingBlock(i);

            if (llvm::dyn_cast<llvm::Constant>(value) != nullptr) {
                operands.push_back(std::make_shared<ConstValue>(*value));
            } else {
                // it must be a register then
                // if it is an already known register, create reg will just return it from lut
                // if not, it creates a new register and will handle it, when it pops up later on the left side of an instruction
                operands.push_back(Register::createRegister(*value));
            } /*
                else {
                std::cerr << "Phi node value type not known!" << block << std::endl;
                value->print(llvm::errs());
                abort();
            }
            */
            std::shared_ptr <BasicBlock> bb = BasicBlock::findBasicBlock(block);
            if (bb == nullptr) { // the basic block does not exist yet
                // create the basic block (it's not added to it's containing function yet though - that will happen, when the parsing finds it)
                // (it won't create another, as it checks for this)
                auto newBasicBlock = std::make_shared<BasicBlock>(*block);
                BasicBlock::addToLut(block, newBasicBlock);
                // newBasicBlock->init();
                operands.push_back(std::make_shared<BasicBlockOperand>(
                        newBasicBlock->getName())); // the constant value name will be the generated name of the basic block
            } else {
                operands.push_back(std::make_shared<BasicBlockOperand>(
                        bb->getName())); // the constant value nam will be the looked up name
            }

        }
        return true;
    } else {
        return false;
    }
}

/**
 * If the instruction is a store or a load, adds one or two string operands (they should be the first operands),
 * namely atomic/volatile/non-atomic and in the atomic case the ordering as well
 *
 * @param inst LLVM instruction
 * @return true if inst is a store or load, false otherwise
 */
bool Instruction::handleOrderingString(llvm::Instruction &inst) {
    std::string isAtomic, ordering = "";
    if(llvm::dyn_cast<llvm::StoreInst>(&inst)!=nullptr) {
        llvm::StoreInst* store = llvm::dyn_cast<llvm::StoreInst>(&inst);
        if(store->isAtomic()) { // atomic
            isAtomic = "atomic";
            ordering = llvm::toIRString(store->getOrdering());
        } else if(store->isVolatile()) { // volatile
            isAtomic = "volatile";
        } else { // not-atomic
            isAtomic = "non-atomic";
        }
        this->operands.push_back(std::make_shared<StringOperand>(isAtomic));
        if(ordering!="") { // atomic case
            this->operands.push_back(std::make_shared<StringOperand>(ordering));
        }
        return true;
    } else if(llvm::dyn_cast<llvm::LoadInst>(&inst)!=nullptr) {
        llvm::LoadInst* load = llvm::dyn_cast<llvm::LoadInst>(&inst);
        if(load->isAtomic()) { // atomic
            isAtomic = "atomic";
            ordering = llvm::toIRString(load->getOrdering());
        } else if(load->isVolatile()) { // volatile
            isAtomic = "volatile";
        } else { // not-atomic
            isAtomic = "non-atomic";
        }
        this->operands.push_back(std::make_shared<StringOperand>(isAtomic));
        if(ordering!="") { // atomic case
            this->operands.push_back(std::make_shared<StringOperand>(ordering));
        }
        return true;
    } else {
        return false;
    }
}

// OperandHandler

bool Instruction::OperandHandler::handleInstruction(llvm::Value *operand, Instruction &inst) {
    if (llvm::dyn_cast<llvm::Instruction>(operand) != nullptr
            || llvm::dyn_cast<llvm::GlobalVariable>(operand) != nullptr) { // the operand is a register, whether it exists yet or not
        inst.operands.push_back(Register::createRegister(*operand));
        return true;
    } else {
        return false;
    }
}

bool Instruction::OperandHandler::handleBasicBlock(llvm::Value *operand, Instruction &inst) {
    llvm::BasicBlock *llvmBbOperand;

    if ((llvmBbOperand = llvm::dyn_cast<llvm::BasicBlock>(operand)) != nullptr) { // the operand is a basic block
        // if it's a basic block, add it to the LUT (if it isn't already there)
        std::shared_ptr <BasicBlock> bb = BasicBlock::findBasicBlock(llvmBbOperand);
        if (bb == nullptr) { // the basic block does not exist yet
            // create the basic block (it's not added to it's containing function yet though - that will happen, when the parsing finds it)
            // (it won't create another, as it checks for this)
            auto newBasicBlock = std::make_shared<BasicBlock>(*llvmBbOperand);
            BasicBlock::addToLut(llvmBbOperand, newBasicBlock);
            // newBasicBlock->init();
            inst.operands.push_back(std::make_shared<BasicBlockOperand>(
                    newBasicBlock->getName())); // the constant value name will be the generated name of the basic block
        } else {
            inst.operands.push_back(std::make_shared<BasicBlockOperand>(
                    bb->getName())); // the constant value nam will be the looked up name
        }
        return true;
    } else {
        return false;
    }
}

bool Instruction::OperandHandler::handleFunction(llvm::Value *operand, Instruction &inst) {
    llvm::Function *llvmFunctionOperand;
    operand = operand->stripPointerCasts();
    if ((llvmFunctionOperand = llvm::dyn_cast<llvm::Function>(operand)) !=
        nullptr) { // the operand is a function (i.e. in a call operation)
        inst.operands.push_back(std::make_shared<StringOperand>(
                llvmFunctionOperand->getName().str())); // the constant value name will be the name of the function
        return true;
    } else {
        return false;
    }
}

bool Instruction::OperandHandler::handleConstant(llvm::Value *operand, Instruction &inst) {
    if (llvm::dyn_cast<llvm::Constant>(operand) !=
        nullptr) { // the operand is a constant (AND not a function - that is also a Constant type in llvm!)
        if (llvm::dyn_cast<llvm::GEPOperator>(operand) != nullptr) {
            llvm::GEPOperator *gep = llvm::dyn_cast<llvm::GEPOperator>(operand);
            inst.operands.push_back(Register::findRegister(gep->getPointerOperand()));
        } else {
            inst.operands.push_back(std::make_shared<ConstValue>(*operand));
        }
        return true;
    } else {
        return false;
    }
}

bool Instruction::OperandHandler::handleFunctionArgument(llvm::Value *operand, Instruction &inst) {
    if (llvm::dyn_cast<llvm::Argument>(operand) != nullptr) {
        // it should be in the register LUT at this point
        inst.operands.push_back(Register::findRegister(operand));
        return true;
    } else {
        return false;
    }
}
