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
/// \file This file describes the various intrinsic functions that
/// Gazer uses for instrumentation.
#ifndef _GAZER_LLVM_INSTRUMENTATION_INTRINSICS_H
#define _GAZER_LLVM_INSTRUMENTATION_INTRINSICS_H

#include <llvm/IR/Instructions.h>
#include <llvm/IR/DebugInfoMetadata.h>

#include <string_view>

namespace gazer {

    class GazerIntrinsic {
    public:
        static llvm::CallInst *CreateInlinedGlobalWrite(llvm::Value *value, llvm::DIGlobalVariable *gv);

    public:
        static llvm::FunctionCallee GetOrInsertInlinedGlobalWrite(llvm::Module &module, llvm::Type *type);

    };

}

#endif