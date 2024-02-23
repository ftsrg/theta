#include "EliminateVariables.h"

/*
 * Eliminates call statements' unused return values.
 * Such functions must not have a name, otherwise verification fails.
 */
bool EliminateVariables::runOnFunction(llvm::Function &F)
{
    for (llvm::Function::iterator FI = F.begin(), E = F.end(); FI != E; ++FI)
    {
        for (llvm::BasicBlock::iterator I = FI->begin(), E = FI->end(); I != E; ++I)
        {
            llvm::CallInst* call;
            if ((call = llvm::dyn_cast<llvm::CallInst>(I)) && I->user_begin() == I->user_end() && call->getType() != llvm::Type::getVoidTy(F.getContext())) {
                call->mutateType(llvm::Type::getVoidTy(F.getContext()));
                call->setValueName(nullptr);
            }
        }
    }
    return false;
}

llvm::Pass *createEliminationPass() {
    return new EliminateVariables();
}