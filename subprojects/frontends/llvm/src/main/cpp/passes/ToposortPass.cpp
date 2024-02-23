//
// Created by solarowl on 4/5/21.
//

#include "ToposortPass.h"

bool ToposortPass::runOnFunction(llvm::Function &f) {
    for (llvm::scc_iterator < llvm::Function * > i = scc_begin(&f); i != scc_end(&f); ++i) {
        const std::vector<llvm::BasicBlock *> stronglyConnectedBbs = *i;
        for (std::vector<llvm::BasicBlock *>::const_iterator j = stronglyConnectedBbs.begin();
             j != stronglyConnectedBbs.end(); ++j) {
            int lastpos = -1;
            for (auto k = pred_begin(*j), kend = pred_end(*j); k != kend; ++k) {
                std::vector<llvm::BasicBlock *>::const_iterator it;
                if ((it = std::find(stronglyConnectedBbs.begin(), stronglyConnectedBbs.end(), *k)) !=
                    stronglyConnectedBbs.end()) {
                    if (it - stronglyConnectedBbs.begin() > lastpos) {
                        lastpos = it - stronglyConnectedBbs.begin();
                    }
                } else {
                    lastpos = -1;
                    break;
                }
            }
            if (lastpos != -1) {
                (*j)->moveAfter(stronglyConnectedBbs.at(lastpos));
            }
        }
    }
    return false;
}

llvm::Pass *createToposortPass() {
    return new ToposortPass();
}
