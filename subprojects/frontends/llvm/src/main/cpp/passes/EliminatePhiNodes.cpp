#include "EliminatePhiNodes.h"
#include <llvm/IR/BasicBlock.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Constants.h>
#include <set>

/*
 * Eliminates phi nodes where it makes sense (no non-dominated predecessor block)
 */
bool EliminatePhiNodes::runOnFunction(llvm::Function &F)
{
    bool first = true;
    llvm::AllocaInst* alloca;
    llvm::DominatorTree domTree{F};
    llvm::IntegerType *Ty = llvm::IntegerType::get(F.getContext(), 64);
    std::set<llvm::BasicBlock*> alreadyStoringPointer;
    for (llvm::Function::iterator FI = F.begin(), E = F.end(); FI != E; ++FI)
    {
        for (llvm::Instruction* I = &*(FI->begin()); I != nullptr; I = I->getNextNonDebugInstruction())
        {
            if(first) {
                
                alloca = new llvm::AllocaInst(Ty, 0, (std::string)"lastblock", &*I);
                first = false;
            }
            llvm::PHINode* phi;
            if ((phi = llvm::dyn_cast<llvm::PHINode>(I))) {
                unsigned num = phi->getNumIncomingValues();
                llvm::Value* val1 = phi->getIncomingValue(0);
                llvm::Value* val2 = phi->getIncomingValue(1);
                llvm::Instruction* inst1, *inst2;
                inst1 = llvm::dyn_cast<llvm::Instruction>(val1);
                inst2 = llvm::dyn_cast<llvm::Instruction>(val2);
                if(num == 2 && ((inst1==nullptr) || domTree.dominates(inst1, phi)) && ((inst2==nullptr) || domTree.dominates(inst2, phi))) {
                    llvm::BasicBlock* incoming = phi->getIncomingBlock(0);
                    llvm::LoadInst* load = new llvm::LoadInst(Ty, alloca, (std::string)"lastblock", &*I);
                    llvm::ConstantInt* constant = llvm::ConstantInt::get(Ty, (long long)incoming);
                    llvm::ICmpInst* icmp = new llvm::ICmpInst(&*I, llvm::CmpInst::Predicate::ICMP_EQ, load, constant);
                    llvm::SelectInst* select = llvm::SelectInst::Create(icmp, phi->getIncomingValue(0), phi->getIncomingValue(1), (std::string)"lastblock");

                    if(alreadyStoringPointer.find(incoming)==alreadyStoringPointer.end()) {
                        new llvm::StoreInst(llvm::ConstantInt::get(Ty, (long long)incoming), alloca, incoming->getTerminator());
                        alreadyStoringPointer.insert(incoming);
                    }
                    llvm::BasicBlock* otherIncoming = phi->getIncomingBlock(1);
                    if(alreadyStoringPointer.find(otherIncoming)==alreadyStoringPointer.end()) {
                        new llvm::StoreInst(llvm::ConstantInt::get(Ty, (long long)otherIncoming), alloca, otherIncoming->getTerminator());
                        alreadyStoringPointer.insert(otherIncoming);
                    }

                    llvm::ReplaceInstWithInst(phi, select);
                    I = select;
                } else if(phi != &*(FI->begin())){
                    I = phi->getPrevNode();
                    phi->moveBefore(&*(FI->begin()));
                }
            }
        }
        
    }
    return false;
}

llvm::Pass *createPhiEliminationPass() {
    return new EliminatePhiNodes();
}