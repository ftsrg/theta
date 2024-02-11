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
#ifndef GAZER_CORE_TRANSFORM_PASSES_H
#define GAZER_CORE_TRANSFORM_PASSES_H

#include <llvm/Pass.h>

namespace gazer {


// Added from LLVMFrontendSettings.h
    enum class InlineLevel {
        Off,        ///< Do not inline procedures
        Default,    ///< Inline non-recursive, used-only-once procedures
        All         ///< Inline all non-recursive procedures
    };

/// A simpler (and more restricted) inlining pass.
    llvm::Pass *createSimpleInlinerPass(llvm::Function &entry, InlineLevel level);

}

#endif
