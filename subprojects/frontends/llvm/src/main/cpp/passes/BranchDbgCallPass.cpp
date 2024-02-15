//
// Created by solarowl on 4/27/21.
//

#include "BranchDbgCallPass.h"

bool BranchDbgCallPass::runOnModule(llvm::Module &M) {
    std::vector < llvm::Type * > funArg = {llvm::Type::getVoidTy(M.getContext())};


    /*
    llvm::FunctionType *FT = llvm::FunctionType::get(llvm::Type::getVoidTy(M.getContext()), funArg, false);
    brDbgFunction = llvm::Function::Create(FT, llvm::Function::ExternalLinkage,
                                           "theta.dbg.control", M);
    */

    llvm::FunctionType *FT = llvm::FunctionType::get(llvm::Type::getVoidTy(M.getContext()), false);
    brDbgFunction = llvm::Function::Create(FT, llvm::Function::ExternalLinkage,
                                               "theta.dbg.control", M);

    brDbgFunction->addFnAttr(llvm::Attribute::AttrKind::WillReturn);
    brDbgFunction->addFnAttr(llvm::Attribute::AttrKind::NoUnwind);
    brDbgFunction->addFnAttr(llvm::Attribute::AttrKind::NoDuplicate);
    // brDbgFunction->addFnAttr(llvm::Attribute::AttrKind::ReadNone);

    auto &llvmFunctionList = M.getFunctionList();
    for (llvm::Function &llvmFunction : llvmFunctionList) {
        if (!llvmFunction.isDeclaration()) {
            iterateOnFunction(llvmFunction);
        }
    }

    return false;
}

void BranchDbgCallPass::handleTerminatorInst(llvm::BasicBlock &bb) {
    llvm::Instruction *term = bb.getTerminator();
    llvm::BranchInst *br;
    if((br=llvm::dyn_cast<llvm::BranchInst>(term))!=nullptr) {
        // create and insert dbg call
        llvm::CallInst::Create(
                brDbgFunction->getFunctionType(),
                brDbgFunction,
                // br->getOperand(0),
                "", // nameStr
                br // insertBefore
        );
    }

}

void BranchDbgCallPass::iterateOnFunction(llvm::Function &F) {
    // iterate through basic blocks
    llvm::BasicBlock *bb = &F.getEntryBlock();
    while (bb) {
        handleTerminatorInst(*bb);
        bb = bb->getNextNode();
    }
}

llvm::Pass *createBranchDbgCallPass() { return new BranchDbgCallPass; }