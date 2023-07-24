//==-------------------------------------------------------------*- C++ -*--==//
//
// Copyright 2019 Contributors to the Gazer project
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//===----------------------------------------------------------------------===//
//
/// \file This file implements our own inlining pass, which is more restricted,
/// but faster than the inlining utilities found in LLVM.
//
//===----------------------------------------------------------------------===//

#include "TransformUtils.h"

#include "Passes.h"

#include <llvm/Pass.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Analysis/InlineCost.h>
#include <llvm/Transforms/Utils/Cloning.h>

#define DEBUG_TYPE "SimplifiedInliner"

using namespace gazer;

namespace {

    class InlinePass : public llvm::ModulePass {
    public:
        static char ID;

    public:
        InlinePass(llvm::Function *entry, InlineLevel level)
                : ModulePass(ID), mEntryFunction(entry), mLevel(level) {
            assert(mEntryFunction != nullptr);
        }

        void getAnalysisUsage(llvm::AnalysisUsage &au) const override {
            au.addRequired<llvm::CallGraphWrapperPass>();
        }

        bool runOnModule(llvm::Module &module) override;

        llvm::StringRef getPassName() const override {
            return "Simplified inling";
        }

    private:
        bool shouldInlineFunction(llvm::CallGraphNode *target, unsigned allowedRefs);

        llvm::Function *mEntryFunction;
        InlineLevel mLevel;
    };

} // end anonymous namespace

char InlinePass::ID;

bool InlinePass::shouldInlineFunction(llvm::CallGraphNode *target, unsigned allowedRefs) {
    bool viable = llvm::isInlineViable(*target->getFunction()).isSuccess();
    viable |= !isRecursive(target);

    if (target->getFunction()->getName() == "reach_error") {
        return false;
    }

    if (!viable) {
        return false;
    }

    if (mLevel == InlineLevel::All) {
        // This setting requires inlining all non-recursive viable calls.
        return true;
    }

    // On the default setting we only want to inline functions which are
    // non-recursive, used only once and do not have variable argument lists.
    if (target->getFunction()->isVarArg()) {
        return false;
    }

    // If the target has fewer references than the threshold, inline it.
    if (target->getNumReferences() <= allowedRefs) {
        return true;
    }

    // Check the function if it is small enough the inline it below the threshold.

    return false;
}

bool InlinePass::runOnModule(llvm::Module &module) {
    if (mLevel == InlineLevel::Off) {
        return false;
    }

    bool changed = false;
    llvm::CallGraph &cg = getAnalysis<llvm::CallGraphWrapperPass>().getCallGraph();

    llvm::InlineFunctionInfo ifi(&cg);
    llvm::SmallVector < llvm::CallBase * , 16 > wl;

    llvm::CallGraphNode *entryCG = cg[mEntryFunction];

    for (auto &tup : *entryCG) {
        auto &call = tup.first;
        auto &target = tup.second;
        if (this->shouldInlineFunction(target, 1)) {
            LLVM_DEBUG(llvm::dbgs() << "Decided to inline call " << *call << " to target "
                                    << target->getFunction()->getName() << "\n");
            wl.emplace_back(llvm::dyn_cast<llvm::CallBase>(*call));
        }
    }

    while (!wl.empty()) {
        llvm::CallBase *cs = wl.pop_back_val();
        bool success = llvm::InlineFunction(*cs, ifi).isSuccess();
        changed |= success;

        for (llvm::Value *newCall : ifi.InlinedCalls) {
            llvm::CallBase *newCS = llvm::dyn_cast<llvm::CallBase>(newCall);
            auto callee = newCS->getCalledFunction();
            if (callee == nullptr) {
                continue;
            }

            llvm::CallGraphNode *calleeNode = cg[callee];
            if (this->shouldInlineFunction(calleeNode, 2)) {
                wl.emplace_back(newCS);
            }
        }
    }

    return changed;
}

llvm::Pass *gazer::createSimpleInlinerPass(llvm::Function &entry, InlineLevel level) {
    return new InlinePass(&entry, level);
}
