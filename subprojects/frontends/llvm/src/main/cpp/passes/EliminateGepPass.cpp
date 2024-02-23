//
// Created by solarowl on 4/5/21.
//

#include "EliminateGepPass.h"
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

// This pass tries to eliminate load/store+gep combinations and changes them to function calls
// some more special cases are also handled (2-3 long chain of geps, bitcast between load/store and gep), but not all of them
bool EliminateGepPass::checkGep(llvm::Instruction* gep) {
    if(gep == nullptr) return false; // not a gep, if nullptr

    if(gep->getNumOperands()!=3 && gep->getNumOperands()!=2) { // it's a gep, but can we handle it?
        std::cerr << "WARNING: Unhandled gep structure, not eliminating instruction" << std::endl;
        std::cerr << "GEP Instruction: " << std::endl;
        gep->print(llvm::errs());
        std::cerr << std::endl;
        /*
        std::cerr << std::endl << "Operands:" << std::endl;
        for(int i = 0; i < gep->getNumOperands(); i++) {
            std::cout << i << ": " << std::endl;
            gep->getOperand(i)->print(llvm::errs());
            std::cout << std::endl;
        }
        */
        return false;
    } else {
        return true;
    }
}

// replaces the given instruction with a call, then returns the newly inserted call instruction
// (which instruction should get as a value, as the old instruction will no longer be valid!)
llvm::Instruction* EliminateGepPass::insertGetArrayElementCall(llvm::Instruction *instruction, llvm::Instruction *gep) {
    llvm::BasicBlock &bb = *instruction->getParent();
    llvm::Value *operand2;
    if(gep->getNumOperands()==3) { // index operands in the form: 0, operand2
        operand2 = gep->getOperand(2);
    } else if(gep->getNumOperands()==2) { // index operands in the form: operand2 (in case of a malloc)
        operand2 = gep->getOperand(1);
    }

    std::vector < llvm::Value * > operands = {
            gep->getOperand(0), // array
            operand2 // idx
    };

    llvm::Function *getArrayElementFunction = fetchGetArrayElementFunction(instruction->getType(),
                                                                           { gep->getOperand(0)->getType(),
                                                                           operand2->getType() },
                                                                           *instruction->getModule());
    llvm::Instruction *ci = llvm::CallInst::Create(
            getArrayElementFunction->getFunctionType(),
            getArrayElementFunction,
            operands,
            ""
    );
    llvm::BasicBlock::iterator ii(instruction);
    llvm::ReplaceInstWithInst(bb.getInstList(), ii, ci);
    instruction = ci;
    removable.insert(gep);
    return instruction;
}

// replaces the given instruction with a call, then returns the newly inserted call instruction
// (which instruction should get as a value, as the old instruction will no longer be valid!)
llvm::Instruction* EliminateGepPass::insertSetArrayElementCall(llvm::Instruction *instruction, llvm::Instruction *gep) {
    llvm::BasicBlock &bb = *instruction->getParent();

    llvm::Value *operand2;
    if(gep->getNumOperands()==3) { // index operands in the form: 0, operand2
        operand2 = gep->getOperand(2);
    } else if(gep->getNumOperands()==2) { // index operands in the form: operand2 (in case of a malloc)
        operand2 = gep->getOperand(1);
    }

    std::vector < llvm::Value * > operands = {
            gep->getOperand(0), // array
            operand2, // idx
            instruction->getOperand(0) // value to set
    };

    llvm::Function *setArrayElementFunction = fetchSetArrayElementFunction( { gep->getOperand(0)->getType(),
                                                                              operand2->getType(),
                                                                              instruction->getOperand(0)->getType()
                                                                            },
                                                                            *instruction->getModule());
    llvm::Instruction *ci = llvm::CallInst::Create(
            setArrayElementFunction->getFunctionType(),
            setArrayElementFunction,
            operands,
            ""
    );

    llvm::BasicBlock::iterator ii(instruction);
    llvm::ReplaceInstWithInst(bb.getInstList(), ii, ci);
    instruction = ci;
    removable.insert(gep);
    return instruction;
}

// (instruction should get the return value as a value, as the old instruction will no longer be valid!)
llvm::Instruction* EliminateGepPass::handleLoad(llvm::Instruction *instruction) {
    llvm::Instruction *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(instruction->getOperand(0));

    if(checkGep(gep)) {
        // there can be a chain of geps, we'll handle double and triple here for now

        /* // TODO debug gep chaings - they cause badrefs
        llvm::Instruction *gep2 = llvm::dyn_cast<llvm::GetElementPtrInst>(gep->getOperand(0));
        if(checkGep(gep2)) {

            llvm::Instruction *gep3 = llvm::dyn_cast<llvm::GetElementPtrInst>(gep2->getOperand(0));
            if(checkGep(gep3)) {
                gep2 = insertGetArrayElementCall(gep2, gep3);
            }

            gep = insertGetArrayElementCall(gep, gep2);
        }
        */
        instruction = insertGetArrayElementCall(instruction, gep);
    } else { // we'll just not handle gep chain+bitcast combinations for now - I'm not even sure, if they exist
        if(gep==nullptr) {
            // handle if there is a bitcast inbetween the load and the gep
            llvm::Instruction *bitcast = llvm::dyn_cast<llvm::BitCastInst>(instruction->getOperand(0));
            if(bitcast != nullptr) {
                gep = llvm::dyn_cast<llvm::GetElementPtrInst>(bitcast->getOperand(0));
                if(checkGep(gep)) { // we got a gep and we can handle its structure
                    gep->getOperand(0)->mutateType(bitcast->getType());
                    instruction = insertGetArrayElementCall(instruction, gep);
                    removable.insert(bitcast);
                }
            }
        }
    }

    return instruction;
}

// (instruction should get the return value as a value, as the old instruction will no longer be valid!)
llvm::Instruction* EliminateGepPass::handleStore(llvm::Instruction *instruction) {
    llvm::Instruction *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(instruction->getOperand(1));

    if (checkGep(gep)) {
        // there can be a chain of geps, we'll handle double and triple here for now
        /* // TODO debug gep chains - they cause badrefs
        llvm::Instruction *gep2 = llvm::dyn_cast<llvm::GetElementPtrInst>(gep->getOperand(0));
        if(checkGep(gep2)) {

            llvm::Instruction *gep3 = llvm::dyn_cast<llvm::GetElementPtrInst>(gep2->getOperand(0));
            if(checkGep(gep3)) {
                gep2 = insertSetArrayElementCall(gep2, gep3);
            }

            gep = insertSetArrayElementCall(gep, gep2);
        }
        */

        instruction = insertSetArrayElementCall(instruction, gep);
    } else {
        llvm::Instruction *bitcast = llvm::dyn_cast<llvm::BitCastInst>(instruction->getOperand(0));

        if(bitcast != nullptr) {
            gep = llvm::dyn_cast<llvm::GetElementPtrInst>(bitcast->getOperand(0)); // handle, if there is a bitcast inbetween the load and the gep
            if(checkGep(gep)) {
                gep->getOperand(0)->mutateType(bitcast->getType());
                instruction = insertSetArrayElementCall(instruction, gep);
                removable.insert(bitcast);
            }
        }
    }

    return instruction;
}

llvm::Function *EliminateGepPass::fetchGetArrayElementFunction(llvm::Type *retType, std::array<llvm::Type*, 2> paramType, llvm::Module &M) {
    std::vector < llvm::Type * > funArg = {paramType[0],
                                           paramType[1]};
    llvm::FunctionType *FT = llvm::FunctionType::get(retType, funArg, false);

    auto getFunc = getElementFunctions.find(FT);
    if (getFunc == getElementFunctions.end()) { // this function does not exist yet, we'll need to add it
        std::string typeName;
        llvm::raw_string_ostream typeNameStream(typeName);
        retType->print(typeNameStream);
        typeNameStream.str();

        llvm::Function *F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage,
                                                   "theta.dbg.getArrayElement_" + std::to_string(getElementFunctions.size()), M);
        getElementFunctions[FT] = F;
        return F;
    } else {
        return getFunc->second;
    }
}

llvm::Function *EliminateGepPass::fetchSetArrayElementFunction(std::array<llvm::Type*, 3> paramType, llvm::Module &M) {
    std::vector < llvm::Type * > funArg = {paramType[0], paramType[1], paramType[2] };
    llvm::FunctionType *FT = llvm::FunctionType::get(llvm::Type::getVoidTy(M.getContext()), funArg, false);
    auto setFunc = setElementFunctions.find(FT);

    if (setFunc == setElementFunctions.end()) { // this function does not exist yet, we'll need to add it
        // create and add setArrayElement function
        llvm::Function *F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage,
                                      "theta.dbg.setArrayElement_" + std::to_string(setElementFunctions.size()), M);

        setElementFunctions[FT] = F;
        return F;
    } else {
        return setFunc->second;
    }
}

void EliminateGepPass::iterateOnBasicBlock(llvm::BasicBlock &bb) {
    llvm::Instruction *instruction = bb.getFirstNonPHI();
    while (instruction != nullptr) {
        if ((std::string) instruction->getOpcodeName() == "load") {
            instruction = handleLoad(instruction);

        } else if ((std::string) instruction->getOpcodeName() == "store") {
            instruction = handleStore(instruction);
        }
        instruction = instruction->getNextNonDebugInstruction();
    }

}

void EliminateGepPass::iterateOnFunction(llvm::Function &F) {
    // iterate through basic blocks
    llvm::BasicBlock *bb = &F.getEntryBlock();
    while (bb) {
        iterateOnBasicBlock(*bb);
        bb = bb->getNextNode();
    }
}

bool EliminateGepPass::runOnModule(llvm::Module &M) {
    // initialize getArrayElement func map
    getElementFunctions = std::unordered_map<llvm::FunctionType *, llvm::Function *>();
    setElementFunctions = std::unordered_map<llvm::FunctionType *, llvm::Function *>();

    removable = std::set<llvm::Instruction *>(); // initialize set

    auto &llvmFunctionList = M.getFunctionList();
    for (llvm::Function &llvmFunction : llvmFunctionList) {
        if (!llvmFunction.isDeclaration()) {
            iterateOnFunction(llvmFunction);
        }
    }


    for (llvm::Instruction *r : removable) {
        if (r != nullptr && r->getParent() != nullptr) {
            r->eraseFromParent();
        }
    }

    return false;
}


llvm::Pass *createEliminateGepPass() { return new EliminateGepPass; }