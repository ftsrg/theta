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

#include "Intrinsics.h"

#include <llvm/IR/Module.h>

using namespace gazer;

static std::string getOverloadedFunctionName(llvm::StringRef prefix, llvm::Type *type) {
    assert(type != nullptr);

    std::string nameBuffer;
    llvm::raw_string_ostream rso(nameBuffer);
    rso << prefix;
    type->print(rso, false, true);
    rso.flush();

    return rso.str();
}

llvm::FunctionCallee GazerIntrinsic::GetOrInsertInlinedGlobalWrite(llvm::Module &module, llvm::Type *type) {
    return module.getOrInsertFunction(
            getOverloadedFunctionName("gazer.inlined_global.write.", type),
            // getOverloadedFunctionName(InlinedGlobalWritePrefix, type), // TODO debug this undefined ref to Intrinsics.h
            llvm::Type::getVoidTy(module.getContext()),
            type,
            llvm::Type::getMetadataTy(module.getContext())
    );
}