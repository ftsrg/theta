//
// Created by solarowl on 4/3/21.
//

#ifndef JNI_LIBRARY_UNDEFTONONDET_H
#define JNI_LIBRARY_UNDEFTONONDET_H

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

#include <llvm/Pass.h>

namespace gazer {

/// This pass turns undef values into nondetermistic functions calls,
/// forcing the optimizer to be more careful around undefined behavior.
    class UndefToNondetCallPass : public llvm::ModulePass {
    public:
        static char ID;

        UndefToNondetCallPass()
                : ModulePass(ID) {}

        bool runOnModule(llvm::Module &module) override;
    };

    llvm::Pass *createPromoteUndefsPass();

}

#endif //JNI_LIBRARY_UNDEFTONONDET_H
